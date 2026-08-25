use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use der::{Decode, Encode};
use vest_lib2::core::exec::{Parser, Prepare, SerializerExt};
use vps_asn1_runtime_eval::{generated_cms_ber, generated_cms_der};

mod corpora {
    include!(concat!(env!("OUT_DIR"), "/cms_corpora.rs"));
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

/// Extract the complete SignedData TLV from ContentInfo without normalizing its BER framing.
fn signed_data(input: &[u8]) -> &[u8] {
    assert_eq!(input.first(), Some(&0x30));
    let (outer, _) = header(input, 0).unwrap();
    assert_eq!(input[outer], 0x06);
    let explicit = tlv_end(input, outer).unwrap();
    assert_eq!(input[explicit], 0xa0);
    let (inner, _) = header(input, explicit).unwrap();
    let end = tlv_end(input, inner).unwrap();
    &input[inner..end]
}

fn inputs(corpus: &'static [(&'static str, &'static [u8])]) -> Vec<&'static [u8]> {
    corpus.iter().map(|(_, input)| signed_data(input)).collect()
}

fn combined_inputs() -> Vec<&'static [u8]> {
    corpora::PKITS
        .iter()
        .chain(corpora::DSS)
        .chain(corpora::RFC4134)
        .map(|(_, input)| signed_data(input))
        .collect()
}

fn validate_der(inputs: &[&[u8]]) {
    for input in inputs {
        assert_eq!(
            generated_cms_der::SIGNED_DATA::Fmt.parse(input).unwrap().0,
            input.len()
        );
        rasn::der::decode::<rasn_cms::SignedData>(input).unwrap();
        rustcrypto_cms::signed_data::SignedData::from_der(input).unwrap();
    }
}

fn validate_ber(inputs: &[&[u8]]) {
    for input in inputs {
        assert_eq!(
            generated_cms_ber::SIGNED_DATA::Fmt.parse(input).unwrap().0,
            input.len()
        );
        rasn::ber::decode::<rasn_cms::SignedData>(input).unwrap();
        rustcrypto_cms::signed_data::SignedData::from_ber(input).unwrap();
    }
}

fn parse_der(c: &mut Criterion, name: &str, corpus: &'static [(&'static str, &'static [u8])]) {
    let inputs = inputs(corpus);
    validate_der(&inputs);
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    eprintln!(
        "CMS {name} corpus: {} values, {} bytes",
        inputs.len(),
        bytes
    );
    let mut group = c.benchmark_group(format!("cms_corpus/{name}/parse"));
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    generated_cms_der::SIGNED_DATA::Fmt
                        .parse(black_box(input))
                        .unwrap(),
                );
            }
        })
    });
    group.bench_function("rasn-cms", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(rasn::der::decode::<rasn_cms::SignedData>(black_box(input)).unwrap());
            }
        })
    });
    group.bench_function("RustCrypto-cms", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    rustcrypto_cms::signed_data::SignedData::from_der(black_box(input)).unwrap(),
                );
            }
        })
    });
    group.finish();
}

fn parse_ber(c: &mut Criterion, name: &str, inputs: Vec<&'static [u8]>) {
    validate_ber(&inputs);
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    eprintln!(
        "CMS {name} corpus: {} values, {} bytes",
        inputs.len(),
        bytes
    );
    let mut group = c.benchmark_group(format!("cms_corpus/{name}/parse"));
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    generated_cms_ber::SIGNED_DATA::Fmt
                        .parse(black_box(input))
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

fn serialize_der(c: &mut Criterion, name: &str, corpus: &'static [(&'static str, &'static [u8])]) {
    let inputs = inputs(corpus);
    validate_der(&inputs);
    let vps_values: Vec<_> = inputs
        .iter()
        .map(|x| generated_cms_der::SIGNED_DATA::Fmt.parse(x).unwrap().1)
        .collect();
    let rasn_values: Vec<_> = inputs
        .iter()
        .map(|x| rasn::der::decode::<rasn_cms::SignedData>(x).unwrap())
        .collect();
    let rustcrypto_values: Vec<_> = inputs
        .iter()
        .map(|x| rustcrypto_cms::signed_data::SignedData::from_der(x).unwrap())
        .collect();
    let lengths: Vec<_> = vps_values
        .iter()
        .map(|x| generated_cms_der::SIGNED_DATA::Fmt.prepare(x).unwrap())
        .collect();
    let bytes = lengths.iter().map(|len| *len as u64).sum();
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut vps_outputs: Vec<_> = lengths.iter().map(|len| vec![0; *len]).collect();
    let mut rasn_output = Vec::with_capacity(capacity);
    let mut rustcrypto_output = vec![0; capacity];
    let mut group = c.benchmark_group(format!("cms_corpus/{name}/serialize"));
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for (value, output) in vps_values.iter().zip(&mut vps_outputs) {
                generated_cms_der::SIGNED_DATA::Fmt
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
    group.finish();
}

fn serialize_ber(c: &mut Criterion, name: &str, inputs: Vec<&'static [u8]>) {
    validate_ber(&inputs);
    let vps_values: Vec<_> = inputs
        .iter()
        .map(|x| generated_cms_ber::SIGNED_DATA::Fmt.parse(x).unwrap().1)
        .collect();
    let rasn_values: Vec<_> = inputs
        .iter()
        .map(|x| rasn::ber::decode::<rasn_cms::SignedData>(x).unwrap())
        .collect();
    let rustcrypto_values: Vec<_> = inputs
        .iter()
        .map(|x| rustcrypto_cms::signed_data::SignedData::from_ber(x).unwrap())
        .collect();
    let lengths: Vec<_> = vps_values
        .iter()
        .map(|x| generated_cms_ber::SIGNED_DATA::Fmt.prepare(x).unwrap())
        .collect();
    let bytes = lengths.iter().map(|len| *len as u64).sum();
    let capacity = inputs.iter().map(|x| x.len()).max().unwrap_or(0) + 1024;
    let mut vps_outputs: Vec<_> = lengths.iter().map(|len| vec![0; *len]).collect();
    let mut rasn_output = Vec::with_capacity(capacity);
    let mut rustcrypto_output = vec![0; capacity];
    let mut group = c.benchmark_group(format!("cms_corpus/{name}/serialize"));
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for (value, output) in vps_values.iter().zip(&mut vps_outputs) {
                generated_cms_ber::SIGNED_DATA::Fmt
                    .serialize(value, black_box(output.as_mut_slice()));
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

fn parse(c: &mut Criterion) {
    parse_ber(c, "pkits", inputs(corpora::PKITS));
    parse_ber(c, "dss-cades", inputs(corpora::DSS));
    parse_ber(c, "rfc4134", inputs(corpora::RFC4134));
    parse_ber(c, "combined", combined_inputs());
}

fn serialize(c: &mut Criterion) {
    serialize_ber(c, "pkits", inputs(corpora::PKITS));
    serialize_ber(c, "dss-cades", inputs(corpora::DSS));
    serialize_ber(c, "rfc4134", inputs(corpora::RFC4134));
    serialize_ber(c, "combined", combined_inputs());
}

criterion_group!(benches, parse, serialize);
criterion_main!(benches);
