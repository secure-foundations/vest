use ciborium::value::Value;
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use serde::Serialize;
use vest_lib2::cbor::CborFmt;
use vest_lib2::core::exec::{Parser, Prepare, SerializerExt};

fn nested(depth: usize, seed: i64) -> Value {
    if depth == 0 {
        Value::Integer(seed.into())
    } else {
        Value::Map(vec![
            (
                Value::Text("depth".into()),
                Value::Integer((depth as i64).into()),
            ),
            (Value::Text("payload".into()), nested(depth - 1, seed)),
            (Value::Text("ok".into()), Value::Bool(depth % 2 == 0)),
        ])
    }
}

fn corpus_values() -> Vec<Value> {
    let mut values = Vec::new();
    for seed in 0..256i64 {
        values.push(Value::Integer(seed.into()));
        values.push(Value::Integer((-seed - 1).into()));
        values.push(Value::Bytes(
            (0..(seed as usize % 128))
                .map(|i| (i ^ seed as usize) as u8)
                .collect(),
        ));
        values.push(Value::Text(format!(
            "VPS-CBOR-{seed:04}-{}",
            "x".repeat(seed as usize % 96)
        )));
        values.push(Value::Array(
            (0..(seed as usize % 24))
                .map(|i| Value::Integer(((seed as usize * 31 + i) as i64).into()))
                .collect(),
        ));
        values.push(nested(4, seed));
    }
    values
}

fn canonical(value: &Value) -> Vec<u8> {
    let mut bytes = Vec::new();
    ciborium::into_writer(value, &mut bytes).unwrap();
    bytes
}

fn cbor_head(major: u8, argument: usize) -> Vec<u8> {
    let mut out = vec![(major << 5) | 27];
    out.extend_from_slice(&(argument as u64).to_be_bytes());
    out
}

fn fragmented(major: u8, bytes: &[u8]) -> Vec<u8> {
    let first = bytes.len() / 3;
    let second = bytes.len() * 2 / 3;
    let mut out = vec![(major << 5) | 31];
    for chunk in [&bytes[..first], &bytes[first..second], &bytes[second..]] {
        out.extend_from_slice(&cbor_head(major, chunk.len()));
        out.extend_from_slice(chunk);
    }
    out.push(0xff);
    out
}

fn widen_integer(bytes: &[u8]) -> Vec<u8> {
    let major = bytes[0] >> 5;
    let additional = bytes[0] & 31;
    let argument = match additional {
        0..=23 => additional as u64,
        24 => bytes[1] as u64,
        25 => u16::from_be_bytes(bytes[1..3].try_into().unwrap()) as u64,
        26 => u32::from_be_bytes(bytes[1..5].try_into().unwrap()) as u64,
        27 => u64::from_be_bytes(bytes[1..9].try_into().unwrap()),
        _ => unreachable!(),
    };
    let mut out = vec![(major << 5) | 27];
    out.extend_from_slice(&argument.to_be_bytes());
    out
}

fn indefinite_container(value: &Value, recursive: bool) -> Vec<u8> {
    match value {
        Value::Array(items) => {
            let mut out = vec![0x9f];
            for item in items {
                out.extend(if recursive {
                    malleable(item, true)
                } else {
                    canonical(item)
                });
            }
            out.push(0xff);
            out
        }
        Value::Map(entries) => {
            let mut out = vec![0xbf];
            for (key, value) in entries {
                out.extend(canonical(key));
                out.extend(if recursive {
                    malleable(value, true)
                } else {
                    canonical(value)
                });
            }
            out.push(0xff);
            out
        }
        _ => canonical(value),
    }
}

fn malleable(value: &Value, recursive: bool) -> Vec<u8> {
    match value {
        Value::Integer(_) => widen_integer(&canonical(value)),
        Value::Bytes(bytes) => fragmented(2, bytes),
        Value::Text(text) => fragmented(3, text.as_bytes()),
        Value::Array(_) | Value::Map(_) => indefinite_container(value, recursive),
        _ => canonical(value),
    }
}

/// Exercise the non-determinism accepted by general CBOR: deliberately over-wide integer
/// arguments, fragmented byte/text strings, indefinite arrays/maps, and recursively indefinite
/// nested containers. Serializers are subsequently benchmarked on the same logical values and
/// are permitted to normalize these representations.
fn encode_corpus(values: &[Value]) -> Vec<Vec<u8>> {
    values.iter().map(|value| malleable(value, true)).collect()
}

fn validate(values: &[Value], inputs: &[Vec<u8>]) {
    let format = CborFmt::<false>;
    for (expected, input) in values.iter().zip(inputs) {
        let ciborium: Value = ciborium::from_reader(&input[..]).unwrap();
        let cbor4ii: Value = cbor4ii::serde::from_slice(input).unwrap();
        let minicbor: Value = minicbor_serde::from_slice(input).unwrap();
        assert_eq!(&ciborium, expected);
        assert_eq!(&cbor4ii, expected);
        assert_eq!(&minicbor, expected);
        let (consumed, vps) = format.parse(&&input[..]).unwrap();
        assert_eq!(consumed, input.len());
        let len = format.prepare(&vps).unwrap();
        let mut normalized = vec![0; len];
        format.serialize(&vps, &mut normalized);
        let normalized_value: Value = ciborium::from_reader(&normalized[..]).unwrap();
        assert_eq!(&normalized_value, expected);
    }
}

fn parse(c: &mut Criterion) {
    let values = corpus_values();
    let inputs = encode_corpus(&values);
    validate(&values, &inputs);
    let bytes = inputs.iter().map(|x| x.len() as u64).sum();
    eprintln!("CBOR corpus: {} values, {} bytes", inputs.len(), bytes);
    let mut group = c.benchmark_group("generic_cbor/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(CborFmt::<false>.parse(black_box(&&input[..])).unwrap());
            }
        })
    });
    group.bench_function("ciborium", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(ciborium::from_reader::<Value, _>(black_box(&input[..])).unwrap());
            }
        })
    });
    group.bench_function("cbor4ii", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(cbor4ii::serde::from_slice::<Value>(black_box(input)).unwrap());
            }
        })
    });
    group.bench_function("minicbor-serde", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(minicbor_serde::from_slice::<Value>(black_box(input)).unwrap());
            }
        })
    });
    group.finish();
}

fn serialize(c: &mut Criterion) {
    let values = corpus_values();
    let inputs = encode_corpus(&values);
    validate(&values, &inputs);
    let format = CborFmt::<false>;
    let vps_values: Vec<_> = inputs
        .iter()
        .map(|x| format.parse(&&x[..]).unwrap().1)
        .collect();
    let lengths: Vec<_> = vps_values
        .iter()
        .map(|x| format.prepare(x).unwrap())
        .collect();
    let total_bytes = lengths.iter().map(|x| *x as u64).sum();
    let mut vps_outputs: Vec<_> = lengths.iter().map(|x| vec![0; *x]).collect();
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut ciborium_output = Vec::with_capacity(capacity);
    let mut cbor4ii_output = Vec::with_capacity(capacity);
    let mut minicbor_output = Vec::with_capacity(capacity);

    let mut group = c.benchmark_group("generic_cbor/serialize");
    group.throughput(Throughput::Bytes(total_bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for (value, output) in vps_values.iter().zip(&mut vps_outputs) {
                format.serialize(value, black_box(output.as_mut_slice()));
                black_box(&output);
            }
        })
    });
    group.bench_function("ciborium", |b| {
        b.iter(|| {
            for value in &values {
                ciborium_output.clear();
                ciborium::into_writer(black_box(value), &mut ciborium_output).unwrap();
                black_box(&ciborium_output);
            }
        })
    });
    group.bench_function("cbor4ii", |b| {
        b.iter(|| {
            for value in &values {
                cbor4ii_output.clear();
                cbor4ii_output =
                    cbor4ii::serde::to_vec(core::mem::take(&mut cbor4ii_output), black_box(value))
                        .unwrap();
                black_box(&cbor4ii_output);
            }
        })
    });
    group.bench_function("minicbor-serde", |b| {
        b.iter(|| {
            for value in &values {
                minicbor_output.clear();
                let mut serializer = minicbor_serde::Serializer::new(&mut minicbor_output);
                black_box(value).serialize(&mut serializer).unwrap();
                black_box(&minicbor_output);
            }
        })
    });
    group.finish();
}

criterion_group!(benches, parse, serialize);
criterion_main!(benches);
