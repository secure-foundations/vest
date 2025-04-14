#![allow(unused)]

extern crate wasm;

use criterion::Throughput;
use criterion::{black_box, criterion_group, criterion_main, Criterion, BatchSize};

use vest::properties::Combinator;
use wasm::vest_wasm::*;

use wasmparser::{Payload, OperatorsReader};

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

pub const POLYBENCH_C_TESTS_REWRITTEN: &[(&str, &[u8])] = &[
    ("2mm", include_bytes!("data/polybench-c/2mm.wasm.rewritten-2")),
    ("3mm", include_bytes!("data/polybench-c/3mm.wasm.rewritten-2")),
    ("adi", include_bytes!("data/polybench-c/adi.wasm.rewritten-2")),
    ("atax", include_bytes!("data/polybench-c/atax.wasm.rewritten-2")),
    ("bicg", include_bytes!("data/polybench-c/bicg.wasm.rewritten-2")),
    ("cholesky", include_bytes!("data/polybench-c/cholesky.wasm.rewritten-2")),
    ("correlation", include_bytes!("data/polybench-c/correlation.wasm.rewritten-2")),
    ("covariance", include_bytes!("data/polybench-c/covariance.wasm.rewritten-2")),
    ("doitgen", include_bytes!("data/polybench-c/doitgen.wasm.rewritten-2")),
    ("durbin", include_bytes!("data/polybench-c/durbin.wasm.rewritten-2")),
    ("dynprog", include_bytes!("data/polybench-c/dynprog.wasm.rewritten-2")),
    ("fdtd-2d", include_bytes!("data/polybench-c/fdtd-2d.wasm.rewritten-2")),
    ("fdtd-apml", include_bytes!("data/polybench-c/fdtd-apml.wasm.rewritten-2")),
    ("floyd-warshall", include_bytes!("data/polybench-c/floyd-warshall.wasm.rewritten-2")),
    ("gemm", include_bytes!("data/polybench-c/gemm.wasm.rewritten-2")),
    ("gemver", include_bytes!("data/polybench-c/gemver.wasm.rewritten-2")),
    ("gesummv", include_bytes!("data/polybench-c/gesummv.wasm.rewritten-2")),
    ("gramschmidt", include_bytes!("data/polybench-c/gramschmidt.wasm.rewritten-2")),
    ("jacobi-1d-imper", include_bytes!("data/polybench-c/jacobi-1d-imper.wasm.rewritten-2")),
    ("jacobi-2d-imper", include_bytes!("data/polybench-c/jacobi-2d-imper.wasm.rewritten-2")),
    ("lu", include_bytes!("data/polybench-c/lu.wasm.rewritten-2")),
    ("ludcmp", include_bytes!("data/polybench-c/ludcmp.wasm.rewritten-2")),
    ("mvt", include_bytes!("data/polybench-c/mvt.wasm.rewritten-2")),
    ("reg_detect", include_bytes!("data/polybench-c/reg_detect.wasm.rewritten-2")),
    ("seidel-2d", include_bytes!("data/polybench-c/seidel-2d.wasm.rewritten-2")),
    ("symm", include_bytes!("data/polybench-c/symm.wasm.rewritten-2")),
    ("syr2k", include_bytes!("data/polybench-c/syr2k.wasm.rewritten-2")),
    ("syrk", include_bytes!("data/polybench-c/syrk.wasm.rewritten-2")),
    ("trisolv", include_bytes!("data/polybench-c/trisolv.wasm.rewritten-2")),
    ("trmm", include_bytes!("data/polybench-c/trmm.wasm.rewritten-2")),
];

fn wasmparser_parse(bytes: &[u8]) {
    let mut parser = wasmparser::Parser::new(0);
    let mut instrs = vec![];

    for payload in parser.parse_all(bytes) {
        match payload.unwrap() {
            Payload::Version { .. } => {}
            Payload::TypeSection(mut reader) => {
                for c in reader { black_box(c.unwrap()); }
            }
            Payload::ImportSection(mut reader) => {
                for c in reader { black_box(c.unwrap()); }
            }

            Payload::FunctionSection(mut reader) => {
                for c in reader { black_box(c.unwrap()); }
            }

            Payload::TableSection(mut reader) => {
                for c in reader { black_box(c.unwrap()); }
            }

            Payload::MemorySection(mut reader) => {
                for c in reader { black_box(c.unwrap()); }
            }

            Payload::GlobalSection(mut reader) => {
                for c in reader {
                    for d in c.unwrap().init_expr.get_operators_reader() {
                        black_box(d.unwrap());
                    }
                }
            }

            Payload::ExportSection(mut reader) => {
                for c in reader { black_box(c.unwrap()); }
            }

            Payload::ElementSection(mut reader) => {
                for c in reader {
                    black_box(c.unwrap());
                }
            }

            Payload::CodeSectionEntry(body) => {
                for c in body.get_locals_reader().unwrap() { black_box(c.unwrap()); }
                for c in body.get_operators_reader().unwrap() { instrs.push(black_box(c.unwrap())); }
            }

            Payload::DataSection(mut reader) => {
                for c in reader { black_box(c.unwrap()); }
            }

            Payload::CustomSection { .. } => {}
            _ => {}
        }
    }
}

/// Benchmark parsing time of polybench-c tests
fn bench_parse_polybench_c_bulk(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_polybench_c_bulk");
    group.bench_function("vest", |b| b.iter(||
        for (_, bytes) in POLYBENCH_C_TESTS_REWRITTEN {
            module().parse(black_box(bytes)).unwrap();
        }
    ));
    // group.bench_function("rwasm", |b| b.iter(||
    //     for (_, bytes) in POLYBENCH_C_TESTS {
    //         rwasm::parser::parse(black_box(bytes)).unwrap();
    //     }
    // ));
    // group.bench_function("wasmbin", |b| b.iter(||
    //     for (_, bytes) in POLYBENCH_C_TESTS {
    //         wasmbin::Module::decode_from(*bytes).unwrap();
    //     }
    // ));
    group.bench_function("wasmparser", |b| b.iter(||
        for (_, bytes) in POLYBENCH_C_TESTS {
            wasmparser_parse(black_box(bytes));
        }
    ));
    group.finish();
}

criterion_group!(
    benches,
    bench_parse_polybench_c_bulk,
);
criterion_main!(benches);
