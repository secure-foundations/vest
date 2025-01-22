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
    ("2mm", include_bytes!("data/polybench-c/2mm.wasm.rewritten")),
    ("3mm", include_bytes!("data/polybench-c/3mm.wasm.rewritten")),
    ("adi", include_bytes!("data/polybench-c/adi.wasm.rewritten")),
    ("atax", include_bytes!("data/polybench-c/atax.wasm.rewritten")),
    ("bicg", include_bytes!("data/polybench-c/bicg.wasm.rewritten")),
    ("cholesky", include_bytes!("data/polybench-c/cholesky.wasm.rewritten")),
    ("correlation", include_bytes!("data/polybench-c/correlation.wasm.rewritten")),
    ("covariance", include_bytes!("data/polybench-c/covariance.wasm.rewritten")),
    ("doitgen", include_bytes!("data/polybench-c/doitgen.wasm.rewritten")),
    ("durbin", include_bytes!("data/polybench-c/durbin.wasm.rewritten")),
    ("dynprog", include_bytes!("data/polybench-c/dynprog.wasm.rewritten")),
    ("fdtd-2d", include_bytes!("data/polybench-c/fdtd-2d.wasm.rewritten")),
    ("fdtd-apml", include_bytes!("data/polybench-c/fdtd-apml.wasm.rewritten")),
    ("floyd-warshall", include_bytes!("data/polybench-c/floyd-warshall.wasm.rewritten")),
    ("gemm", include_bytes!("data/polybench-c/gemm.wasm.rewritten")),
    ("gemver", include_bytes!("data/polybench-c/gemver.wasm.rewritten")),
    ("gesummv", include_bytes!("data/polybench-c/gesummv.wasm.rewritten")),
    ("gramschmidt", include_bytes!("data/polybench-c/gramschmidt.wasm.rewritten")),
    ("jacobi-1d-imper", include_bytes!("data/polybench-c/jacobi-1d-imper.wasm.rewritten")),
    ("jacobi-2d-imper", include_bytes!("data/polybench-c/jacobi-2d-imper.wasm.rewritten")),
    ("lu", include_bytes!("data/polybench-c/lu.wasm.rewritten")),
    ("ludcmp", include_bytes!("data/polybench-c/ludcmp.wasm.rewritten")),
    ("mvt", include_bytes!("data/polybench-c/mvt.wasm.rewritten")),
    ("reg_detect", include_bytes!("data/polybench-c/reg_detect.wasm.rewritten")),
    ("seidel-2d", include_bytes!("data/polybench-c/seidel-2d.wasm.rewritten")),
    ("symm", include_bytes!("data/polybench-c/symm.wasm.rewritten")),
    ("syr2k", include_bytes!("data/polybench-c/syr2k.wasm.rewritten")),
    ("syrk", include_bytes!("data/polybench-c/syrk.wasm.rewritten")),
    ("trisolv", include_bytes!("data/polybench-c/trisolv.wasm.rewritten")),
    ("trmm", include_bytes!("data/polybench-c/trmm.wasm.rewritten")),
];

fn wasmparser_parse(bytes: &[u8]) {
    let mut parser = wasmparser::Parser::new(0);

    for payload in parser.parse_all(bytes) {
        match payload.unwrap() {
            Payload::Version { .. } => {}
            Payload::TypeSection(mut reader) => {
                for c in reader { c.unwrap(); }
            }
            Payload::ImportSection(mut reader) => {
                for c in reader { c.unwrap(); }
            }

            Payload::FunctionSection(mut reader) => {
                for c in reader { c.unwrap(); }
            }

            Payload::TableSection(mut reader) => {
                for c in reader { c.unwrap(); }
            }

            Payload::MemorySection(mut reader) => {
                for c in reader { c.unwrap(); }
            }

            Payload::GlobalSection(mut reader) => {
                for c in reader {
                    for d in c.unwrap().init_expr.get_operators_reader() {
                        d.unwrap();
                    }
                }
            }

            Payload::ExportSection(mut reader) => {
                for c in reader { c.unwrap(); }
            }

            Payload::ElementSection(mut reader) => {
                for c in reader {
                    c.unwrap();
                }
            }

            Payload::CodeSectionEntry(body) => {
                for c in body.get_locals_reader().unwrap() { c.unwrap(); }
                for c in body.get_operators_reader().unwrap() { c.unwrap(); }
            }

            Payload::DataSection(mut reader) => {
                for c in reader { c.unwrap(); }
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
    group.bench_function("rwasm", |b| b.iter(||
        for (_, bytes) in POLYBENCH_C_TESTS {
            rwasm::parser::parse(black_box(bytes)).unwrap();
        }
    ));
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
