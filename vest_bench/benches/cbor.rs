//! General-CBOR benchmarks over synthetic malleable values and IETF COSE vectors.

use std::hint::black_box;
use vest_bench::harness::Group;
use vest_bench::real::cbor;

use ciborium::value::Value;
use criterion::{criterion_group, criterion_main, Criterion};
use vest_lib::cbor::CborFmt;
use vest_lib::core::exec::Parser;

fn benchmark(c: &mut Criterion, name: &str, values: Vec<Value>, inputs: Vec<Vec<u8>>) {
    let format = CborFmt::<false>;
    let checked = cbor::validated_values(&values, &inputs);
    let input_bytes = inputs.iter().map(|input| input.len() as u64).sum();
    let mut group = Group::new(c, format!("cbor/{name}/parse"), inputs.len(), input_bytes);
    group.retained("Vest", |i| {
        let (consumed, value) = format.parse(black_box(&inputs[i].as_slice())).unwrap();
        assert_eq!(consumed, inputs[i].len());
        value
    });
    let mut scratch = [0u8; 4096];
    group.retained("ciborium", |i| {
        ciborium::de::from_reader_with_buffer::<Value, _>(black_box(&inputs[i][..]), &mut scratch)
            .unwrap()
    });
    group.retained("cbor4ii", |i| {
        cbor::cbor4ii::parse(black_box(&inputs[i])).unwrap()
    });
    group.retained("minicbor", |i| {
        cbor::minicbor::parse(black_box(&inputs[i])).unwrap()
    });
    group.finish();

    let mut group = Group::serializing(c, format!("cbor/{name}/serialize"), &format, &checked.vest);
    group.retained("ciborium", |i| {
        let mut output = Vec::new();
        ciborium::into_writer(black_box(&values[i]), &mut output).unwrap();
        output
    });
    group.retained("cbor4ii", |i| {
        cbor::cbor4ii::encode(black_box(&checked.cbor4ii[i]))
    });
    group.retained("minicbor", |i| {
        cbor::minicbor::encode(black_box(&checked.minicbor[i]))
    });
    group.finish();
}

fn synthetic(c: &mut Criterion) {
    let values = cbor::synthetic_values();
    let inputs = values.iter().map(cbor::malleable).collect();
    benchmark(c, "synthetic", values, inputs);
}

fn cose(c: &mut Criterion) {
    let inputs = cbor::cose_inputs();
    let values = inputs
        .iter()
        .map(|input| ciborium::from_reader(&input[..]).unwrap())
        .collect();
    // Both native AST adapters preserve tags and borrow contiguous payloads.
    benchmark(c, "cose", values, inputs);
}

criterion_group! { name = benches; config = vest_bench::harness::criterion();
targets = synthetic, cose }
criterion_main!(benches);
