// Copyright 2020 Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::fs::File;
use tempfile::tempfile;
use wasmbin::io::DecodeError;
use wasmbin::visit::{Visit, VisitError};
use wasmbin::Module;

fn deep_module() -> Module {
    use wasmbin::builtins::Blob;
    use wasmbin::instructions::{Expression, Instruction};
    use wasmbin::sections::FuncBody;
    use wasmbin::types::BlockType;

    let mut expr = Expression::default();
    for _ in 0..100_000 {
        expr.push(Instruction::BlockStart(BlockType::Empty));
    }
    for _ in 0..100_000 {
        expr.push(Instruction::End);
    }
    Module {
        sections: vec![vec![Blob::from(FuncBody {
            locals: Default::default(),
            expr,
        })]
        .into()],
        ..Default::default()
    }
}

fn unlazify<T: Visit>(wasm: T) -> Result<T, DecodeError> {
    match wasm.visit(|()| {}) {
        Ok(()) => Ok(wasm),
        Err(err) => match err {
            VisitError::LazyDecode(err) => Err(err),
            VisitError::Custom(err) => match err {},
        },
    }
}

fn bench_parse(c: &mut Criterion) {
    c.bench_function(concat!(stringify!($name), "::bench_parse"), |b| {
        b.iter(|| {
            let f = File::open("benches/fixture.wasm").unwrap();
            unlazify(Module::decode_from(f).unwrap())
        })
    });
}

fn bench_parse_buf(c: &mut Criterion) {
    c.bench_function(concat!(stringify!($name), "::bench_parse_buf"), |b| {
        b.iter(|| {
            let f = File::open("benches/fixture.wasm").unwrap();
            let f = std::io::BufReader::new(f);
            unlazify(Module::decode_from(f).unwrap())
        })
    });
}

fn bench_parse_vec(c: &mut Criterion) {
    c.bench_function(concat!(stringify!($name), "::bench_parse_vec"), |b| {
        let f = std::fs::read("benches/fixture.wasm").unwrap();
        b.iter(|| {
            let f = black_box(f.as_slice());
            unlazify(Module::decode_from(f).unwrap())
        })
    });
}

fn bench_parse_deep_module(c: &mut Criterion) {
    c.bench_function(
        concat!(stringify!($name), "::bench_parse_deep_module"),
        |b| {
            let f = deep_module().encode_into(Vec::new()).unwrap();
            b.iter(|| {
                let f = black_box(f.as_slice());
                unlazify(Module::decode_from(f).unwrap())
            })
        },
    );
}

fn read_module() -> Module {
    let f = std::fs::read("benches/fixture.wasm").unwrap();
    unlazify(Module::decode_from(f.as_slice()).unwrap()).unwrap()
}

fn bench_write(c: &mut Criterion) {
    c.bench_function(concat!(stringify!($name), "::bench_write"), |b| {
        let m = read_module();
        b.iter(|| {
            let f = tempfile().unwrap();
            black_box(&m).encode_into(f).unwrap()
        })
    });
}

fn bench_write_buf(c: &mut Criterion) {
    c.bench_function(concat!(stringify!($name), "::bench_write_buf"), |b| {
        let m = read_module();
        b.iter(|| {
            let f = tempfile().unwrap();
            let f = std::io::BufWriter::new(f);
            black_box(&m).encode_into(f).unwrap()
        })
    });
}

fn bench_write_vec(c: &mut Criterion) {
    c.bench_function(concat!(stringify!($name), "::bench_write_vec"), |b| {
        let m = read_module();
        b.iter(|| black_box(&m).encode_into(Vec::new()).unwrap())
    });
}

fn bench_write_deep_module(c: &mut Criterion) {
    c.bench_function(
        concat!(stringify!($name), "::bench_write_deep_module"),
        |b| {
            let m = deep_module();
            b.iter(|| black_box(&m).encode_into(Vec::new()).unwrap())
        },
    );
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(20);
    targets =
        bench_parse,
        bench_parse_buf,
        bench_parse_vec,
        bench_parse_deep_module,
        bench_write,
        bench_write_buf,
        bench_write_vec,
        bench_write_deep_module,
}

criterion_main!(benches);
