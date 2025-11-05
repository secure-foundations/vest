// extern crate wasmparser;

pub mod vest_wasm;
// pub mod wasm_data;

use vest_lib::properties::*;
use vest_lib::regular::bytes;
use vest_lib::regular::disjoint::DisjointFrom;
use vest_lib::regular::modifier::*;
use vest_lib::regular::repetition::*;
use vest_lib::regular::sequence::*;
use vest_lib::regular::tag::*;
use vest_lib::regular::uints::*;
use vest_lib::regular::variant::*;
use vest_lib::utils::*;
use vest_wasm::*;
// use wasm_data::*;

pub const POLYBENCH_C_TESTS: &[(&str, &[u8])] = &[
    (
        "2mm",
        include_bytes!("../benches/data/polybench-c/2mm.wasm"),
    ),
    (
        "3mm",
        include_bytes!("../benches/data/polybench-c/3mm.wasm"),
    ),
    (
        "adi",
        include_bytes!("../benches/data/polybench-c/adi.wasm"),
    ),
    (
        "atax",
        include_bytes!("../benches/data/polybench-c/atax.wasm"),
    ),
    (
        "bicg",
        include_bytes!("../benches/data/polybench-c/bicg.wasm"),
    ),
    (
        "cholesky",
        include_bytes!("../benches/data/polybench-c/cholesky.wasm"),
    ),
    (
        "correlation",
        include_bytes!("../benches/data/polybench-c/correlation.wasm"),
    ),
    (
        "covariance",
        include_bytes!("../benches/data/polybench-c/covariance.wasm"),
    ),
    (
        "doitgen",
        include_bytes!("../benches/data/polybench-c/doitgen.wasm"),
    ),
    (
        "durbin",
        include_bytes!("../benches/data/polybench-c/durbin.wasm"),
    ),
    (
        "dynprog",
        include_bytes!("../benches/data/polybench-c/dynprog.wasm"),
    ),
    (
        "fdtd-2d",
        include_bytes!("../benches/data/polybench-c/fdtd-2d.wasm"),
    ),
    (
        "fdtd-apml",
        include_bytes!("../benches/data/polybench-c/fdtd-apml.wasm"),
    ),
    (
        "floyd-warshall",
        include_bytes!("../benches/data/polybench-c/floyd-warshall.wasm"),
    ),
    (
        "gemm",
        include_bytes!("../benches/data/polybench-c/gemm.wasm"),
    ),
    (
        "gemver",
        include_bytes!("../benches/data/polybench-c/gemver.wasm"),
    ),
    (
        "gesummv",
        include_bytes!("../benches/data/polybench-c/gesummv.wasm"),
    ),
    (
        "gramschmidt",
        include_bytes!("../benches/data/polybench-c/gramschmidt.wasm"),
    ),
    (
        "jacobi-1d-imper",
        include_bytes!("../benches/data/polybench-c/jacobi-1d-imper.wasm"),
    ),
    (
        "jacobi-2d-imper",
        include_bytes!("../benches/data/polybench-c/jacobi-2d-imper.wasm"),
    ),
    ("lu", include_bytes!("../benches/data/polybench-c/lu.wasm")),
    (
        "ludcmp",
        include_bytes!("../benches/data/polybench-c/ludcmp.wasm"),
    ),
    (
        "mvt",
        include_bytes!("../benches/data/polybench-c/mvt.wasm"),
    ),
    (
        "reg_detect",
        include_bytes!("../benches/data/polybench-c/reg_detect.wasm"),
    ),
    (
        "seidel-2d",
        include_bytes!("../benches/data/polybench-c/seidel-2d.wasm"),
    ),
    (
        "symm",
        include_bytes!("../benches/data/polybench-c/symm.wasm"),
    ),
    (
        "syr2k",
        include_bytes!("../benches/data/polybench-c/syr2k.wasm"),
    ),
    (
        "syrk",
        include_bytes!("../benches/data/polybench-c/syrk.wasm"),
    ),
    (
        "trisolv",
        include_bytes!("../benches/data/polybench-c/trisolv.wasm"),
    ),
    (
        "trmm",
        include_bytes!("../benches/data/polybench-c/trmm.wasm"),
    ),
];

pub const POLYBENCH_C_TESTS_REWRITTEN: &[(&str, &[u8])] = &[
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
    let bench_vest = || {
        for (_, bytes) in POLYBENCH_C_TESTS_REWRITTEN {
            if let Ok((consumed, module)) = module().parse(bytes) {
                // println!("Vest consumed: {}/{}", consumed, bytes.len());
                // println!("{:?}", module);
            } else {
                println!("Vest failed to parse module");
            }
        }
        Ok(())
    };
    // let bench_wasmparser = || {
    //     for (name, bytes) in POLYBENCH_C_TESTS {
    //         // println!("Parsing {}...", name);
    //         if let Ok(module) = Module::parse(bytes) {
    //             // println!("wasmparser parsed module: {:?}", module);
    //         } else {
    //             println!("wasmparser failed to parse module: {}", name);
    //         }
    //     }
    //     Ok(())
    // };
    // for (_, bytes) in POLYBENCH_C_TESTS_REWRITTEN {
    //     if let Ok((consumed, module)) = module().parse(bytes) {
    //         println!("Consumed: {}/{}", consumed, bytes.len());
    //         // println!("{:?}", module);
    //     } else {
    //         println!("Vest failed to parse module");
    //     }
    //     // let (consumed, _) = module().parse(bytes)?;
    //     // println!("Consumed: {}/{}", consumed, bytes.len());
    //     // println!("{:?}", rwasm::parser::parse(bytes).unwrap());
    // }
    //
    // for (name, bytes) in POLYBENCH_C_TESTS {
    //     println!("Parsing {}...", name);
    //     if let Ok(module) = Module::parse(bytes) {
    //         // println!("Parsed module: {:?}", module);
    //     } else {
    //         println!("wasmparser failed to parse module: {}", name);
    //     }
    // }
    bench_fn(bench_vest)?;
    // bench_fn(bench_wasmparser)?;

    Ok(())
}

fn bench_fn(
    f: impl Fn() -> Result<(), Box<dyn std::error::Error>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let start = std::time::Instant::now();
    for _ in 0..100 {
        f()?;
    }
    println!("Time elapsed: {} ms", start.elapsed().as_millis());

    Ok(())
}
