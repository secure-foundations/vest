//! General-CBOR benchmarks over synthetic malleable values and IETF COSE vectors.

use std::hint::black_box;
use vest_bench::harness::Group;
use vest_bench::real::cbor::{self, Baselines};

use ciborium::value::Value;
use criterion::{criterion_group, criterion_main, Criterion};
use serde::Serialize;
use vest_lib::cbor::CborFmt;
use vest_lib::core::exec::Parser;

fn benchmark(
    c: &mut Criterion,
    name: &str,
    values: Vec<Value>,
    inputs: Vec<Vec<u8>>,
    baselines: Baselines,
) {
    let format = CborFmt::<false>;
    let checked = cbor::validated_values(&values, &inputs, baselines);
    let input_bytes = inputs.iter().map(|input| input.len() as u64).sum();
    let mut group = Group::new(c, format!("cbor/{name}/parse"), inputs.len(), input_bytes);
    group.retained("Vest", |i| {
        format.parse(black_box(&inputs[i].as_slice())).unwrap()
    });
    let mut scratch = [0u8; 4096];
    group.retained("ciborium", |i| {
        ciborium::de::from_reader_with_buffer::<Value, _>(black_box(&inputs[i][..]), &mut scratch)
            .unwrap()
    });
    if baselines.supports_cbor4ii_parse() {
        group.retained("cbor4ii", |i| cbor::cbor4ii_parse(black_box(&inputs[i])));
    }
    if baselines.supports_minicbor() {
        group.retained("minicbor-serde", |i| {
            minicbor_serde::from_slice::<Value>(black_box(&inputs[i])).unwrap()
        });
    }
    group.finish();

    let mut group = Group::serializing(c, format!("cbor/{name}/serialize"), &format, &checked.vest);
    group.retained("ciborium", |i| {
        let mut output = Vec::new();
        ciborium::into_writer(black_box(&values[i]), &mut output).unwrap();
        output
    });
    group.retained("cbor4ii", |i| {
        cbor::cbor4ii_encode(black_box(&checked.cbor4ii[i]))
    });
    if baselines.supports_minicbor() {
        group.retained("minicbor-serde", |i| {
            let mut output = Vec::new();
            let mut serializer = minicbor_serde::Serializer::new(&mut output);
            black_box(&values[i]).serialize(&mut serializer).unwrap();
            output
        });
    }
    group.finish();
}

fn synthetic(c: &mut Criterion) {
    let values = cbor::synthetic_values();
    let inputs = values.iter().map(cbor::malleable).collect();
    // cbor4ii 1.2.3 leaves indefinite-string breaks unread. Do not report
    // incomplete parsing as equivalent work; its serializer still qualifies.
    benchmark(c, "synthetic", values, inputs, Baselines::Fragmented);
}

fn cose(c: &mut Criterion) {
    let inputs = cbor::cose_inputs();
    let values = inputs
        .iter()
        .map(|input| ciborium::from_reader(&input[..]).unwrap())
        .collect();
    // cbor4ii's native value supports tags; the minicbor-serde bridge does not.
    benchmark(c, "cose", values, inputs, Baselines::Tagged);
}

criterion_group! { name = benches; config = vest_bench::harness::criterion();
targets = synthetic, cose }
criterion_main!(benches);
