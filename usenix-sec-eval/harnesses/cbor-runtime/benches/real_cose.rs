use ciborium::value::Value;
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use std::fs;
use std::path::{Path, PathBuf};
use vest_lib2::cbor::CborFmt;
use vest_lib2::core::exec::{Parser, Prepare, SerializerExt};

fn decode_hex(text: &str) -> Vec<u8> {
    let compact: Vec<_> = text
        .bytes()
        .filter(|byte| !byte.is_ascii_whitespace())
        .collect();
    assert_eq!(compact.len() % 2, 0);
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

fn corpus() -> Vec<Vec<u8>> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../corpora/cbor/cose-wg");
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

fn validate(inputs: &[Vec<u8>]) -> Vec<Value> {
    let format = CborFmt::<false>;
    inputs
        .iter()
        .map(|input| {
            let expected: Value = ciborium::from_reader(&input[..]).unwrap();
            let (consumed, parsed) = format.parse(&&input[..]).unwrap();
            assert_eq!(consumed, input.len());
            let len = format.prepare(&parsed).unwrap();
            let mut normalized = vec![0; len];
            format.serialize(&parsed, &mut normalized);
            let normalized_value: Value = ciborium::from_reader(&normalized[..]).unwrap();
            assert_eq!(normalized_value, expected);
            expected
        })
        .collect()
}

fn parse(c: &mut Criterion) {
    let inputs = corpus();
    let _values = validate(&inputs);
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    eprintln!(
        "COSE WG CBOR corpus: {} values, {} bytes",
        inputs.len(),
        bytes
    );
    let mut group = c.benchmark_group("real_cose_cbor/parse");
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
    group.finish();
}

fn serialize(c: &mut Criterion) {
    let inputs = corpus();
    let values = validate(&inputs);
    let format = CborFmt::<false>;
    let vps_values: Vec<_> = inputs
        .iter()
        .map(|input| format.parse(&&input[..]).unwrap().1)
        .collect();
    let lengths: Vec<_> = vps_values
        .iter()
        .map(|value| format.prepare(value).unwrap())
        .collect();
    let bytes = lengths.iter().map(|len| *len as u64).sum();
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut vps_outputs: Vec<_> = lengths.iter().map(|len| vec![0; *len]).collect();
    let mut ciborium_output = Vec::with_capacity(capacity);
    let mut group = c.benchmark_group("real_cose_cbor/serialize");
    group.throughput(Throughput::Bytes(bytes));
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
    group.finish();
}

criterion_group!(benches, parse, serialize);
criterion_main!(benches);
