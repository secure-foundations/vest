#![allow(unused)]

extern crate wasm;

use criterion::Throughput;
use criterion::{black_box, criterion_group, criterion_main, Criterion, BatchSize};

use vest::properties::Combinator;
use wasm::vest_wasm::*;

pub const POLYBENCH_C_TESTS: &[(&str, &[u8])] = &[
    ("2mm", include_bytes!("data/polybench-c/2mm.wasm")),
    ("3mm", include_bytes!("data/polybench-c/3mm.wasm")),
    ("adi", include_bytes!("data/polybench-c/adi.wasm")),
    ("atax", include_bytes!("data/polybench-c/atax.wasm")),
    ("bicg", include_bytes!("data/polybench-c/bicg.wasm")),
    ("cholesky", include_bytes!("data/polybench-c/cholesky.wasm")),
    ("correlation", include_bytes!("data/polybench-c/correlation.wasm")),
    ("covariance", include_bytes!("data/polybench-c/covariance.wasm")),
    ("doitgen", include_bytes!("data/polybench-c/doitgen.wasm")),
    ("durbin", include_bytes!("data/polybench-c/durbin.wasm")),
    ("dynprog", include_bytes!("data/polybench-c/dynprog.wasm")),
    ("fdtd-2d", include_bytes!("data/polybench-c/fdtd-2d.wasm")),
    ("fdtd-apml", include_bytes!("data/polybench-c/fdtd-apml.wasm")),
    ("floyd-warshall", include_bytes!("data/polybench-c/floyd-warshall.wasm")),
    ("gemm", include_bytes!("data/polybench-c/gemm.wasm")),
    ("gemver", include_bytes!("data/polybench-c/gemver.wasm")),
    ("gesummv", include_bytes!("data/polybench-c/gesummv.wasm")),
    ("gramschmidt", include_bytes!("data/polybench-c/gramschmidt.wasm")),
    ("jacobi-1d-imper", include_bytes!("data/polybench-c/jacobi-1d-imper.wasm")),
    ("jacobi-2d-imper", include_bytes!("data/polybench-c/jacobi-2d-imper.wasm")),
    ("lu", include_bytes!("data/polybench-c/lu.wasm")),
    ("ludcmp", include_bytes!("data/polybench-c/ludcmp.wasm")),
    ("mvt", include_bytes!("data/polybench-c/mvt.wasm")),
    ("reg_detect", include_bytes!("data/polybench-c/reg_detect.wasm")),
    ("seidel-2d", include_bytes!("data/polybench-c/seidel-2d.wasm")),
    ("symm", include_bytes!("data/polybench-c/symm.wasm")),
    ("syr2k", include_bytes!("data/polybench-c/syr2k.wasm")),
    ("syrk", include_bytes!("data/polybench-c/syrk.wasm")),
    ("trisolv", include_bytes!("data/polybench-c/trisolv.wasm")),
    ("trmm", include_bytes!("data/polybench-c/trmm.wasm")),
];

/// Benchmark parsing time of polybench-c tests
fn bench_parse_polybench_c_bulk(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_polybench_c_bulk");
    group.bench_function("vest", |b| b.iter(||
        for (_, bytes) in POLYBENCH_C_TESTS {
            module().parse(black_box(bytes)).unwrap();
        }
    ));
    group.bench_function("rwasm", |b| b.iter(||
        for (_, bytes) in POLYBENCH_C_TESTS {
            rwasm::parser::parse(black_box(bytes)).unwrap();
        }
    ));
    group.bench_function("wasmparser", |b| b.iter(||
        for (_, bytes) in POLYBENCH_C_TESTS {
            let mut parser = wasmparser::Parser::new(0);
            for payload in parser.parse_all(black_box(bytes)) {
                payload.unwrap();
            }
        }
    ));
    group.finish();
}

criterion_group!(
    benches,
    bench_parse_polybench_c_bulk,
);
criterion_main!(benches);
