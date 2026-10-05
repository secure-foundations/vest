//! CMS benchmarks over a synthetic ContentInfo workload and three public corpora.

use std::fs;
use std::hint::black_box;
use std::path::{Path, PathBuf};

use bcder::{decode::Constructed, encode::Values, Mode};
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use der::{Decode, Encode};
use vest_asn1_tests::generated_cms;
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

fn der_len(len: usize) -> Vec<u8> {
    if len < 128 {
        vec![len as u8]
    } else {
        let bytes = len.to_be_bytes();
        let first = bytes.iter().position(|byte| *byte != 0).unwrap();
        let mut out = vec![0x80 | (bytes.len() - first) as u8];
        out.extend_from_slice(&bytes[first..]);
        out
    }
}

fn tlv(tag: u8, body: &[u8]) -> Vec<u8> {
    let mut out = vec![tag];
    out.extend_from_slice(&der_len(body.len()));
    out.extend_from_slice(body);
    out
}

fn synthetic_content_info() -> Vec<Vec<u8>> {
    (0..1024usize)
        .map(|seed| {
            let payload: Vec<_> = (0..seed % 512)
                .map(|i| (seed.wrapping_mul(29) ^ i.wrapping_mul(17)) as u8)
                .collect();
            let mut body = vec![
                0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x07, 0x01,
            ];
            body.extend_from_slice(&tlv(0xa0, &tlv(0x04, &payload)));
            tlv(0x30, &body)
        })
        .collect()
}

fn parse_bcder(input: &[u8]) -> cryptographic_message_syntax::asn1::rfc5652::ContentInfo {
    Constructed::decode(input, Mode::Der, |cons| {
        cons.take_sequence(cryptographic_message_syntax::asn1::rfc5652::ContentInfo::from_sequence)
    })
    .unwrap()
}

fn header(input: &[u8], offset: usize) -> Option<(usize, Option<usize>)> {
    let mut pos = offset + 1;
    if input.get(offset)? & 31 == 31 {
        while input.get(pos)? & 0x80 != 0 {
            pos += 1;
        }
        pos += 1;
    }
    let first = *input.get(pos)?;
    pos += 1;
    if first == 0x80 {
        return Some((pos, None));
    }
    if first & 0x80 == 0 {
        return Some((pos, Some(first as usize)));
    }
    let count = (first & 0x7f) as usize;
    let mut len = 0usize;
    for byte in input.get(pos..pos + count)? {
        len = (len << 8) | *byte as usize;
    }
    Some((pos + count, Some(len)))
}

fn tlv_end(input: &[u8], offset: usize) -> Option<usize> {
    let (start, len) = header(input, offset)?;
    if let Some(len) = len {
        return start.checked_add(len).filter(|end| *end <= input.len());
    }
    let mut pos = start;
    loop {
        if input.get(pos..pos + 2)? == [0, 0] {
            return Some(pos + 2);
        }
        pos = tlv_end(input, pos)?;
    }
}

fn signed_data(input: &[u8]) -> Option<&[u8]> {
    let (outer, _) = header(input, 0)?;
    let explicit = tlv_end(input, outer)?;
    let (inner, _) = header(input, explicit)?;
    let end = tlv_end(input, inner)?;
    input.get(inner..end)
}

fn visit_cms(dir: &Path, inputs: &mut Vec<Vec<u8>>) {
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            visit_cms(&path, inputs);
        } else if path.extension().is_some_and(|extension| extension == "cms") {
            let file = fs::read(path).unwrap();
            if let Some(value) = signed_data(&file) {
                inputs.push(value.to_vec());
            }
        }
    }
}

fn real_signed_data() -> Vec<Vec<u8>> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("corpora/cms");
    let mut inputs = Vec::new();
    visit_cms(&root.join("pkits"), &mut inputs);
    visit_cms(&root.join("dss"), &mut inputs);
    visit_cms(&root.join("rfc4134"), &mut inputs);
    inputs
}

fn synthetic(c: &mut Criterion) {
    let inputs = synthetic_content_info();
    for input in &inputs {
        assert_eq!(
            generated_cms::CONTENT_INFO::Fmt
                .parse(&&input[..])
                .unwrap()
                .0,
            input.len()
        );
        rasn::ber::decode::<rasn_cms::ContentInfo>(input).unwrap();
        rustcrypto_cms::content_info::ContentInfo::from_ber(input).unwrap();
        parse_bcder(input);
    }
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    let mut group = c.benchmark_group("cms/content_info/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    generated_cms::CONTENT_INFO::Fmt
                        .parse(black_box(&&input[..]))
                        .unwrap(),
                );
            }
        })
    });
    group.bench_function("rasn-cms", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(rasn::ber::decode::<rasn_cms::ContentInfo>(black_box(input)).unwrap());
            }
        })
    });
    group.bench_function("RustCrypto-cms", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    rustcrypto_cms::content_info::ContentInfo::from_ber(black_box(input)).unwrap(),
                );
            }
        })
    });
    group.bench_function("cryptographic-message-syntax", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(parse_bcder(black_box(input)));
            }
        })
    });
    group.finish();
}

fn synthetic_serialize(c: &mut Criterion) {
    let inputs = synthetic_content_info();
    let vest_values: Vec<_> = inputs
        .iter()
        .map(|input| {
            generated_cms::CONTENT_INFO::Fmt
                .parse(&&input[..])
                .unwrap()
                .1
        })
        .collect();
    let rasn_values: Vec<_> = inputs
        .iter()
        .map(|input| rasn::der::decode::<rasn_cms::ContentInfo>(input).unwrap())
        .collect();
    let rustcrypto_values: Vec<_> = inputs
        .iter()
        .map(|input| rustcrypto_cms::content_info::ContentInfo::from_der(input).unwrap())
        .collect();
    let bcder_values: Vec<_> = inputs.iter().map(|input| parse_bcder(input)).collect();
    let lengths: Vec<_> = vest_values
        .iter()
        .map(|value| generated_cms::CONTENT_INFO::Fmt.prepare(value).unwrap())
        .collect();
    let bytes = lengths.iter().map(|length| *length as u64).sum();
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut vest_outputs: Vec<_> = lengths.iter().map(|length| vec![0; *length]).collect();
    let mut rasn_output = Vec::with_capacity(capacity);
    let mut rustcrypto_output = vec![0; capacity];
    let mut bcder_output = Vec::with_capacity(capacity);
    let mut group = c.benchmark_group("cms/content_info/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for (value, output) in vest_values.iter().zip(&mut vest_outputs) {
                generated_cms::CONTENT_INFO::Fmt.serialize(value, black_box(output.as_mut_slice()));
                black_box(&output);
            }
        })
    });
    group.bench_function("rasn-cms", |b| {
        b.iter(|| {
            for value in &rasn_values {
                rasn::der::encode_buf(black_box(value), &mut rasn_output).unwrap();
                black_box(&rasn_output);
            }
        })
    });
    group.bench_function("RustCrypto-cms", |b| {
        b.iter(|| {
            for value in &rustcrypto_values {
                black_box(value.encode_to_slice(&mut rustcrypto_output).unwrap());
            }
        })
    });
    group.bench_function("cryptographic-message-syntax", |b| {
        b.iter(|| {
            for value in &bcder_values {
                bcder_output.clear();
                black_box(value)
                    .write_encoded(Mode::Der, &mut bcder_output)
                    .unwrap();
                black_box(&bcder_output);
            }
        })
    });
    group.finish();
}

fn real_parse(c: &mut Criterion) {
    let inputs = real_signed_data();
    assert!(!inputs.is_empty());
    for input in &inputs {
        assert_eq!(
            generated_cms::SIGNED_DATA::Fmt
                .parse(&&input[..])
                .unwrap()
                .0,
            input.len()
        );
        rasn::ber::decode::<rasn_cms::SignedData>(input).unwrap();
        rustcrypto_cms::signed_data::SignedData::from_ber(input).unwrap();
    }
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    let mut group = c.benchmark_group("cms/real_signed_data/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    generated_cms::SIGNED_DATA::Fmt
                        .parse(black_box(&&input[..]))
                        .unwrap(),
                );
            }
        })
    });
    group.bench_function("rasn-cms", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(rasn::ber::decode::<rasn_cms::SignedData>(black_box(input)).unwrap());
            }
        })
    });
    group.bench_function("RustCrypto-cms", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    rustcrypto_cms::signed_data::SignedData::from_ber(black_box(input)).unwrap(),
                );
            }
        })
    });
    group.finish();
}

fn real_serialize(c: &mut Criterion) {
    let inputs = real_signed_data();
    let vest_values: Vec<_> = inputs
        .iter()
        .map(|input| {
            generated_cms::SIGNED_DATA::Fmt
                .parse(&&input[..])
                .unwrap()
                .1
        })
        .collect();
    let rasn_values: Vec<_> = inputs
        .iter()
        .map(|input| rasn::ber::decode::<rasn_cms::SignedData>(input).unwrap())
        .collect();
    let rustcrypto_values: Vec<_> = inputs
        .iter()
        .map(|input| rustcrypto_cms::signed_data::SignedData::from_ber(input).unwrap())
        .collect();
    let lengths: Vec<_> = vest_values
        .iter()
        .map(|value| generated_cms::SIGNED_DATA::Fmt.prepare(value).unwrap())
        .collect();
    let bytes = lengths.iter().map(|length| *length as u64).sum();
    let mut vest_outputs: Vec<_> = lengths.iter().map(|length| vec![0; *length]).collect();
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut rasn_output = Vec::with_capacity(capacity);
    let mut rustcrypto_output = vec![0; capacity];
    let mut group = c.benchmark_group("cms/real_signed_data/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for (value, output) in vest_values.iter().zip(&mut vest_outputs) {
                generated_cms::SIGNED_DATA::Fmt.serialize(value, black_box(output.as_mut_slice()));
                black_box(&output);
            }
        })
    });
    group.bench_function("rasn-cms", |b| {
        b.iter(|| {
            for value in &rasn_values {
                rasn::ber::encode_buf(black_box(value), &mut rasn_output).unwrap();
                black_box(&rasn_output);
            }
        })
    });
    group.bench_function("RustCrypto-cms", |b| {
        b.iter(|| {
            for value in &rustcrypto_values {
                black_box(value.encode_to_slice(&mut rustcrypto_output).unwrap());
            }
        })
    });
    group.finish();
}

criterion_group!(
    benches,
    synthetic,
    synthetic_serialize,
    real_parse,
    real_serialize
);
criterion_main!(benches);
