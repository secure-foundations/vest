use bcder::{decode::Constructed, encode::Values, Mode};
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use der::{Decode, Encode};
use vest_lib2::core::exec::{Parser, Prepare, SerializerExt};
use vps_asn1_runtime_eval::generated_cms_der;

fn der_len(len: usize) -> Vec<u8> {
    if len < 128 {
        vec![len as u8]
    } else {
        let bytes = len.to_be_bytes();
        let first = bytes.iter().position(|x| *x != 0).unwrap();
        let significant = &bytes[first..];
        let mut out = vec![0x80 | significant.len() as u8];
        out.extend_from_slice(significant);
        out
    }
}

fn tlv(tag: u8, body: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(1 + 9 + body.len());
    out.push(tag);
    out.extend_from_slice(&der_len(body.len()));
    out.extend_from_slice(body);
    out
}

fn content_info(payload: &[u8]) -> Vec<u8> {
    // id-data = 1.2.840.113549.1.7.1
    let oid = [
        0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x07, 0x01,
    ];
    let octets = tlv(0x04, payload);
    let explicit = tlv(0xa0, &octets);
    let mut body = oid.to_vec();
    body.extend_from_slice(&explicit);
    tlv(0x30, &body)
}

fn corpus() -> Vec<Vec<u8>> {
    (0..1024usize)
        .map(|seed| {
            let payload: Vec<_> = (0..(seed % 512))
                .map(|i| (seed.wrapping_mul(29) ^ i.wrapping_mul(17)) as u8)
                .collect();
            content_info(&payload)
        })
        .collect()
}

fn parse_bcder(input: &[u8]) -> cryptographic_message_syntax::asn1::rfc5652::ContentInfo {
    // This table is DER-only. Decoding in DER mode also records a DER capture,
    // which bcder permits us to serialize again in DER mode.
    Constructed::decode(input, Mode::Der, |cons| {
        cons.take_sequence(cryptographic_message_syntax::asn1::rfc5652::ContentInfo::from_sequence)
    })
    .unwrap()
}

fn validate(inputs: &[Vec<u8>]) {
    for input in inputs {
        assert_eq!(
            generated_cms_der::CONTENT_INFO::Fmt
                .parse(&&input[..])
                .unwrap()
                .0,
            input.len()
        );
        rasn::der::decode::<rasn_cms::ContentInfo>(input).unwrap();
        rustcrypto_cms::content_info::ContentInfo::from_der(input).unwrap();
        parse_bcder(input);
    }
}

fn parse(c: &mut Criterion) {
    let inputs = corpus();
    validate(&inputs);
    let bytes = inputs.iter().map(|x| x.len() as u64).sum();
    eprintln!(
        "CMS ContentInfo corpus: {} values, {} bytes",
        inputs.len(),
        bytes
    );
    let mut group = c.benchmark_group("cms_content_info/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    generated_cms_der::CONTENT_INFO::Fmt
                        .parse(black_box(&&input[..]))
                        .unwrap(),
                );
            }
        })
    });
    group.bench_function("rasn-cms", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(rasn::der::decode::<rasn_cms::ContentInfo>(black_box(input)).unwrap());
            }
        })
    });
    group.bench_function("RustCrypto-cms", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    rustcrypto_cms::content_info::ContentInfo::from_der(black_box(input)).unwrap(),
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

fn serialize(c: &mut Criterion) {
    let inputs = corpus();
    validate(&inputs);
    let vps_values: Vec<_> = inputs
        .iter()
        .map(|x| {
            generated_cms_der::CONTENT_INFO::Fmt
                .parse(&&x[..])
                .unwrap()
                .1
        })
        .collect();
    let rasn_values: Vec<_> = inputs
        .iter()
        .map(|x| rasn::der::decode::<rasn_cms::ContentInfo>(x).unwrap())
        .collect();
    let rustcrypto_values: Vec<_> = inputs
        .iter()
        .map(|x| rustcrypto_cms::content_info::ContentInfo::from_der(x).unwrap())
        .collect();
    let bcder_values: Vec<_> = inputs.iter().map(|x| parse_bcder(x)).collect();
    let lengths: Vec<_> = vps_values
        .iter()
        .map(|x| generated_cms_der::CONTENT_INFO::Fmt.prepare(x).unwrap())
        .collect();
    let bytes = lengths.iter().map(|x| *x as u64).sum();
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut vps_outputs: Vec<_> = lengths.iter().map(|x| vec![0; *x]).collect();
    let mut rasn_output = Vec::with_capacity(capacity);
    let mut rustcrypto_output = vec![0; capacity];
    let mut bcder_output = Vec::with_capacity(capacity);
    let mut group = c.benchmark_group("cms_content_info/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for (value, output) in vps_values.iter().zip(&mut vps_outputs) {
                generated_cms_der::CONTENT_INFO::Fmt
                    .serialize(value, black_box(output.as_mut_slice()));
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

criterion_group!(benches, parse, serialize);
criterion_main!(benches);
