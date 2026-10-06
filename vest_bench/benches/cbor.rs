//! General-CBOR benchmarks over synthetic malleable values and IETF COSE vectors.

use std::fs;
use std::hint::black_box;
use std::path::{Path, PathBuf};

use ciborium::value::Value;
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use serde::Serialize;
use vest_lib::cbor::CborFmt;
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

#[path = "support/cbor.rs"]
mod checks;

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

fn synthetic_values() -> Vec<Value> {
    let mut values = Vec::new();
    for seed in 0..256i64 {
        values.push(Value::Integer(seed.into()));
        values.push(Value::Integer((-seed - 1).into()));
        values.push(Value::Bytes(
            (0..seed as usize % 128)
                .map(|i| (i ^ seed as usize) as u8)
                .collect(),
        ));
        values.push(Value::Text(format!(
            "Vest-CBOR-{seed:04}-{}",
            "x".repeat(seed as usize % 96)
        )));
        values.push(Value::Array(
            (0..seed as usize % 24)
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

fn malleable(value: &Value) -> Vec<u8> {
    match value {
        Value::Integer(_) => {
            let bytes = canonical(value);
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
        Value::Bytes(bytes) => fragmented(2, bytes),
        Value::Text(text) => fragmented(3, text.as_bytes()),
        Value::Array(items) => {
            let mut out = vec![0x9f];
            for item in items {
                out.extend(malleable(item));
            }
            out.push(0xff);
            out
        }
        Value::Map(entries) => {
            let mut out = vec![0xbf];
            for (key, value) in entries {
                out.extend(canonical(key));
                out.extend(malleable(value));
            }
            out.push(0xff);
            out
        }
        _ => canonical(value),
    }
}

fn decode_hex(text: &str) -> Vec<u8> {
    let compact: Vec<_> = text
        .bytes()
        .filter(|byte| !byte.is_ascii_whitespace())
        .collect();
    assert_eq!(compact.len() % 2, 0, "odd-length hex input");
    compact
        .chunks_exact(2)
        .map(|pair| {
            let digit = |byte: u8| match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'f' => byte - b'a' + 10,
                b'A'..=b'F' => byte - b'A' + 10,
                _ => panic!("invalid hex digit"),
            };
            digit(pair[0]) << 4 | digit(pair[1])
        })
        .collect()
}

fn visit_json(dir: &Path, paths: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            visit_json(&path, paths);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "json")
        {
            paths.push(path);
        }
    }
}

fn cose_inputs() -> Vec<Vec<u8>> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("corpora/cbor/cose-wg");
    let mut paths = Vec::new();
    visit_json(&root, &mut paths);
    paths.sort();
    paths
        .into_iter()
        .filter_map(|path| {
            let document: serde_json::Value =
                serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
            document
                .pointer("/output/cbor")
                .and_then(|value| value.as_str())
                .map(decode_hex)
        })
        .collect()
}

fn benchmark(
    c: &mut Criterion,
    name: &str,
    values: Vec<Value>,
    inputs: Vec<Vec<u8>>,
    baselines: Baselines,
) {
    let serde_baselines = !matches!(baselines, Baselines::Tagged);
    let cbor4ii_parse = matches!(baselines, Baselines::All);
    let format = CborFmt::<false>;
    assert!(!inputs.is_empty());
    assert_eq!(values.len(), inputs.len());
    for (expected, input) in values.iter().zip(&inputs) {
        assert_eq!(&checks::ciborium_exact(input), expected);
        if serde_baselines {
            if cbor4ii_parse {
                assert_eq!(&checks::cbor4ii_exact(input), expected);
            }
            assert_eq!(&checks::minicbor_exact(input), expected);
        }
        let (n, value) = format.parse(&&input[..]).unwrap();
        assert_eq!(n, input.len());
        assert_eq!(&checks::semantic_value(&value), expected);
    }
    let input_bytes = inputs.iter().map(|input| input.len() as u64).sum();
    let mut group = c.benchmark_group(format!("cbor/{name}/parse"));
    group.throughput(Throughput::Bytes(input_bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(format.parse(black_box(&&input[..])).unwrap());
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
    if cbor4ii_parse {
        group.bench_function("cbor4ii", |b| {
            b.iter(|| {
                for input in &inputs {
                    black_box(cbor4ii::serde::from_slice::<Value>(black_box(input)).unwrap());
                }
            })
        });
    }
    if serde_baselines {
        group.bench_function("minicbor-serde", |b| {
            b.iter(|| {
                for input in &inputs {
                    black_box(minicbor_serde::from_slice::<Value>(black_box(input)).unwrap());
                }
            })
        });
    }
    group.finish();

    let vest_values: Vec<_> = inputs
        .iter()
        .map(|input| format.parse(&&input[..]).unwrap().1)
        .collect();
    let lengths: Vec<_> = vest_values
        .iter()
        .map(|value| format.prepare(value).unwrap())
        .collect();
    let output_bytes = lengths.iter().map(|length| *length as u64).sum();
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut vest_output = vec![0; capacity];
    let mut ciborium_output = Vec::with_capacity(capacity);
    let mut cbor4ii_output = Vec::with_capacity(capacity);
    let mut minicbor_output = Vec::with_capacity(capacity);
    for ((value, expected), length) in vest_values.iter().zip(&values).zip(&lengths) {
        format.serialize(value, &mut vest_output[..*length]);
        assert_eq!(&checks::ciborium_exact(&vest_output[..*length]), expected);
        ciborium_output.clear();
        ciborium::into_writer(expected, &mut ciborium_output).unwrap();
        assert_eq!(&vest_output[..*length], &ciborium_output);
        if serde_baselines {
            cbor4ii_output.clear();
            cbor4ii_output = cbor4ii::serde::to_vec(cbor4ii_output, expected).unwrap();
            assert_eq!(&vest_output[..*length], &cbor4ii_output);
            minicbor_output.clear();
            expected
                .serialize(&mut minicbor_serde::Serializer::new(&mut minicbor_output))
                .unwrap();
            assert_eq!(&vest_output[..*length], &minicbor_output);
        }
    }
    let mut group = c.benchmark_group(format!("cbor/{name}/serialize"));
    group.throughput(Throughput::Bytes(output_bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for (value, length) in vest_values.iter().zip(&lengths) {
                format.serialize(black_box(value), black_box(&mut vest_output[..*length]));
                black_box(&vest_output[..*length]);
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
    if serde_baselines {
        group.bench_function("cbor4ii", |b| {
            b.iter(|| {
                for value in &values {
                    cbor4ii_output.clear();
                    cbor4ii_output = cbor4ii::serde::to_vec(
                        core::mem::take(&mut cbor4ii_output),
                        black_box(value),
                    )
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
    }
    group.finish();
}

fn synthetic(c: &mut Criterion) {
    let values = synthetic_values();
    let inputs = values.iter().map(malleable).collect();
    // cbor4ii 1.2.3 leaves indefinite-string breaks unread. Do not report
    // incomplete parsing as equivalent work; its serializer still qualifies.
    benchmark(c, "synthetic", values, inputs, Baselines::Fragmented);
}

fn synthetic_definite(c: &mut Criterion) {
    let values = synthetic_values();
    let inputs = values.iter().map(canonical).collect();
    benchmark(c, "synthetic_definite", values, inputs, Baselines::All);
}

fn cose(c: &mut Criterion) {
    let inputs = cose_inputs();
    let values = inputs
        .iter()
        .map(|input| ciborium::from_reader(&input[..]).unwrap())
        .collect();
    // COSE values use CBOR tags, which the serde bridges in cbor4ii and
    // minicbor-serde cannot preserve through ciborium's generic Value type.
    benchmark(c, "cose", values, inputs, Baselines::Tagged);
}

enum Baselines {
    All,
    Fragmented,
    Tagged,
}

criterion_group!(benches, synthetic, synthetic_definite, cose);
criterion_main!(benches);
