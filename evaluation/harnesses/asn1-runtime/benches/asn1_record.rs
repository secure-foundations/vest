use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use der::{
    asn1::{OctetString as DerOctetString, OctetStringRef, Utf8StringRef},
    Decode, Encode, Sequence,
};
use rasn::types::{OctetString, Utf8String};
use rasn::Decoder as _;
use vps_lib::core::exec::{Parser, Prepare, SerializerExt};
use vps_asn1_runtime_eval::{generated_ber, generated_der};

#[derive(Clone, Debug, PartialEq, rasn::AsnType, rasn::Decode, rasn::Encode)]
struct RasnRecord {
    enabled: bool,
    counter: i64,
    payload: OctetString,
    label: Utf8String,
    values: Vec<i64>,
}

#[derive(Clone, Debug, Eq, PartialEq, Sequence)]
struct RustCryptoDerRecord<'a> {
    enabled: bool,
    counter: i64,
    payload: &'a OctetStringRef,
    label: Utf8StringRef<'a>,
    values: Vec<i64>,
}

#[derive(Clone, Debug, Eq, PartialEq, Sequence)]
struct RustCryptoBerRecord {
    enabled: bool,
    counter: i64,
    payload: DerOctetString,
    label: String,
    values: Vec<i64>,
}

fn values() -> Vec<RasnRecord> {
    (0..1024i64)
        .map(|seed| RasnRecord {
            enabled: seed % 2 == 0,
            counter: seed - 512,
            payload: (0..(seed as usize % 192))
                .map(|i| (i.wrapping_mul(17) ^ seed as usize) as u8)
                .collect::<Vec<_>>()
                .into(),
            label: format!("record-{seed:04}-{}", "x".repeat(seed as usize % 48)),
            values: (0..(seed as usize % 20)).map(|i| seed + i as i64).collect(),
        })
        .collect()
}

fn der_inputs(values: &[RasnRecord]) -> Vec<Vec<u8>> {
    values
        .iter()
        .map(|value| rasn::der::encode(value).unwrap())
        .collect()
}

fn length_at(input: &[u8], offset: usize) -> (usize, usize) {
    let first = input[offset];
    if first & 0x80 == 0 {
        (first as usize, 1)
    } else {
        let n = (first & 0x7f) as usize;
        let len = input[offset + 1..offset + 1 + n]
            .iter()
            .fold(0usize, |acc, byte| (acc << 8) | *byte as usize);
        (len, n + 1)
    }
}

fn fields(der: &[u8]) -> Vec<&[u8]> {
    assert_eq!(der[0], 0x30);
    let (outer_len, outer_len_len) = length_at(der, 1);
    let mut pos = 1 + outer_len_len;
    let end = pos + outer_len;
    let mut result = Vec::new();
    while pos < end {
        let (len, len_len) = length_at(der, pos + 1);
        let item_end = pos + 1 + len_len + len;
        result.push(&der[pos..item_end]);
        pos = item_end;
    }
    result
}

fn definite(tag: u8, contents: &[u8]) -> Vec<u8> {
    let mut out = vec![tag];
    if contents.len() < 128 {
        out.push(contents.len() as u8);
    } else {
        let bytes = contents.len().to_be_bytes();
        let first = bytes.iter().position(|byte| *byte != 0).unwrap();
        out.push(0x80 | (bytes.len() - first) as u8);
        out.extend_from_slice(&bytes[first..]);
    }
    out.extend_from_slice(contents);
    out
}

fn indefinite(tag: u8, children: &[u8]) -> Vec<u8> {
    let mut out = vec![tag | 0x20, 0x80];
    out.extend_from_slice(children);
    out.extend_from_slice(&[0, 0]);
    out
}

fn record_with_fields(items: &[Vec<u8>], indefinite_length: bool) -> Vec<u8> {
    let contents: Vec<u8> = items.iter().flatten().copied().collect();
    if indefinite_length {
        indefinite(0x30, &contents)
    } else {
        definite(0x30, &contents)
    }
}

fn fragmented_octets(item: &[u8], nested: bool, definite_outer: bool) -> Vec<u8> {
    let (len, len_len) = length_at(item, 1);
    let bytes = &item[1 + len_len..1 + len_len + len];
    let split = bytes.len() / 2;
    let left = definite(0x04, &bytes[..split]);
    let right = definite(0x04, &bytes[split..]);
    let children = if nested {
        [indefinite(0x24, &left), right].concat()
    } else {
        [left, right].concat()
    };
    if definite_outer {
        definite(0x24, &children)
    } else {
        indefinite(0x24, &children)
    }
}

fn fragmented_character_string(item: &[u8]) -> Vec<u8> {
    let (len, len_len) = length_at(item, 1);
    let bytes = &item[1 + len_len..1 + len_len + len];
    let split = bytes.len() / 2;
    let children = [
        definite(0x04, &bytes[..split]),
        definite(0x04, &bytes[split..]),
    ]
    .concat();
    indefinite(item[0] | 0x20, &children)
}

fn nonminimal_length(item: &[u8]) -> Vec<u8> {
    let (len, len_len) = length_at(item, 1);
    let contents = &item[1 + len_len..1 + len_len + len];
    let mut out = vec![item[0], 0x82, 0, len as u8];
    out.extend_from_slice(contents);
    out
}

/// BER forms accepted by all three implementations: DER, indefinite containers, and a
/// one-level constructed-indefinite OCTET STRING. RustCrypto intentionally rejects several
/// additional legal BER alternatives covered by `ber_comprehensive_inputs`.
fn ber_common_inputs(der: &[Vec<u8>]) -> Vec<Vec<u8>> {
    der.iter()
        .enumerate()
        .map(|(i, bytes)| {
            let mut items: Vec<Vec<u8>> = fields(bytes).into_iter().map(<[u8]>::to_vec).collect();
            match i % 4 {
                0 => bytes.clone(),
                1 => record_with_fields(&items, true),
                2 => {
                    items[2] = fragmented_octets(&items[2], false, false);
                    record_with_fields(&items, false)
                }
                _ => {
                    let sequence_items = fields(&items[4]);
                    let contents: Vec<u8> = sequence_items.into_iter().flatten().copied().collect();
                    items[4] = indefinite(0x30, &contents);
                    record_with_fields(&items, true)
                }
            }
        })
        .collect()
}

/// Broader legal BER coverage for VPS and rasn. In addition to the common corpus this includes
/// constructed-definite and recursively fragmented strings, non-minimal lengths, alternative
/// TRUE octets, and nested indefinite containers. VPS intentionally rejects non-minimal INTEGER
/// contents, so those are tested as rejection cases rather than timed successful parses.
fn ber_comprehensive_inputs(values: &[RasnRecord], der: &[Vec<u8>]) -> Vec<Vec<u8>> {
    der.iter()
        .zip(values)
        .enumerate()
        .map(|(i, (bytes, value))| {
            let mut items: Vec<Vec<u8>> = fields(bytes).into_iter().map(<[u8]>::to_vec).collect();
            let outer_indefinite = matches!(i % 11, 1 | 7 | 9);
            match i % 11 {
                0 => {}
                1 => {}
                2 => items[2] = fragmented_octets(&items[2], false, false),
                3 => items[2] = fragmented_octets(&items[2], false, true),
                4 => items[2] = fragmented_octets(&items[2], true, false),
                5 => items[2] = nonminimal_length(&items[2]),
                6 if value.enabled => items[0][2] = 0x01,
                6 => items[1] = nonminimal_length(&items[1]),
                7 | 8 => {
                    let contents: Vec<u8> =
                        fields(&items[4]).into_iter().flatten().copied().collect();
                    items[4] = indefinite(0x30, &contents);
                }
                9 => items[3] = nonminimal_length(&items[3]),
                10 => items[3] = fragmented_character_string(&items[3]),
                _ => {}
            }
            record_with_fields(&items, outer_indefinite)
        })
        .collect()
}

fn validate(values: &[RasnRecord], der: &[Vec<u8>], common: &[Vec<u8>], comprehensive: &[Vec<u8>]) {
    for (((expected, der), common), comprehensive) in
        values.iter().zip(der).zip(common).zip(comprehensive)
    {
        assert_eq!(rasn::der::decode::<RasnRecord>(der).unwrap(), *expected);
        assert_eq!(rasn::ber::decode::<RasnRecord>(common).unwrap(), *expected);
        assert_eq!(
            rasn::ber::decode::<RasnRecord>(comprehensive).unwrap(),
            *expected
        );
        RustCryptoDerRecord::from_der(der).unwrap();
        RustCryptoBerRecord::from_ber(common).unwrap();
        assert_eq!(
            generated_der::EVAL_RECORD::Fmt.parse(&&der[..]).unwrap().0,
            der.len()
        );
        assert_eq!(
            generated_ber::EVAL_RECORD::Fmt
                .parse(&&common[..])
                .unwrap()
                .0,
            common.len()
        );
        assert_eq!(
            generated_ber::EVAL_RECORD::Fmt
                .parse(&&comprehensive[..])
                .unwrap()
                .0,
            comprehensive.len()
        );
    }
}

fn parse_der(c: &mut Criterion) {
    let values = values();
    let inputs = der_inputs(&values);
    let common = ber_common_inputs(&inputs);
    let comprehensive = ber_comprehensive_inputs(&values, &inputs);
    validate(&values, &inputs, &common, &comprehensive);
    let bytes = inputs.iter().map(|x| x.len() as u64).sum();
    eprintln!("ASN.1 DER corpus: {} values, {} bytes", inputs.len(), bytes);
    let mut group = c.benchmark_group("asn1_der/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    generated_der::EVAL_RECORD::Fmt
                        .parse(black_box(&&input[..]))
                        .unwrap(),
                );
            }
        })
    });
    group.bench_function("rasn", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(rasn::der::decode::<RasnRecord>(black_box(input)).unwrap());
            }
        })
    });
    group.bench_function("RustCrypto-der", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(RustCryptoDerRecord::from_der(black_box(input)).unwrap());
            }
        })
    });
    group.finish();
}

fn serialize_der(c: &mut Criterion) {
    let values = values();
    let inputs = der_inputs(&values);
    let vps_values: Vec<_> = inputs
        .iter()
        .map(|x| generated_der::EVAL_RECORD::Fmt.parse(&&x[..]).unwrap().1)
        .collect();
    let rustcrypto_values: Vec<_> = inputs
        .iter()
        .map(|x| RustCryptoDerRecord::from_der(x).unwrap())
        .collect();
    let lengths: Vec<_> = vps_values
        .iter()
        .map(|x| generated_der::EVAL_RECORD::Fmt.prepare(x).unwrap())
        .collect();
    let bytes = lengths.iter().map(|x| *x as u64).sum();
    let mut vps_outputs: Vec<_> = lengths.iter().map(|x| vec![0; *x]).collect();
    let mut rasn_output = Vec::with_capacity(lengths.iter().copied().max().unwrap_or(0));
    let mut rustcrypto_output = vec![0; lengths.iter().copied().max().unwrap_or(0)];
    let mut group = c.benchmark_group("asn1_der/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for (value, output) in vps_values.iter().zip(&mut vps_outputs) {
                generated_der::EVAL_RECORD::Fmt.serialize(value, black_box(output.as_mut_slice()));
                black_box(&output);
            }
        })
    });
    group.bench_function("rasn", |b| {
        b.iter(|| {
            for value in &values {
                rasn::der::encode_buf(black_box(value), &mut rasn_output).unwrap();
                black_box(&rasn_output);
            }
        })
    });
    group.bench_function("RustCrypto-der", |b| {
        b.iter(|| {
            for value in &rustcrypto_values {
                black_box(value.encode_to_slice(&mut rustcrypto_output).unwrap());
            }
        })
    });
    group.finish();
}

fn parse_ber(c: &mut Criterion) {
    let values = values();
    let der = der_inputs(&values);
    let common = ber_common_inputs(&der);
    let inputs = ber_comprehensive_inputs(&values, &der);
    validate(&values, &der, &common, &inputs);

    let common_bytes = common.iter().map(|x| x.len() as u64).sum();
    eprintln!(
        "ASN.1 BER common corpus: {} values, {} bytes",
        common.len(),
        common_bytes
    );
    let mut group = c.benchmark_group("asn1_ber_common/parse");
    group.throughput(Throughput::Bytes(common_bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for input in &common {
                black_box(
                    generated_ber::EVAL_RECORD::Fmt
                        .parse(black_box(&&input[..]))
                        .unwrap(),
                );
            }
        })
    });
    group.bench_function("rasn", |b| {
        b.iter(|| {
            for input in &common {
                black_box(rasn::ber::decode::<RasnRecord>(black_box(input)).unwrap());
            }
        })
    });
    group.bench_function("RustCrypto-ber", |b| {
        b.iter(|| {
            for input in &common {
                black_box(RustCryptoBerRecord::from_ber(black_box(input)).unwrap());
            }
        })
    });
    group.finish();

    let bytes = inputs.iter().map(|x| x.len() as u64).sum();
    eprintln!(
        "ASN.1 BER comprehensive corpus: {} values, {} bytes",
        inputs.len(),
        bytes
    );
    let mut group = c.benchmark_group("asn1_ber_comprehensive/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(
                    generated_ber::EVAL_RECORD::Fmt
                        .parse(black_box(&&input[..]))
                        .unwrap(),
                );
            }
        })
    });
    group.bench_function("rasn", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(rasn::ber::decode::<RasnRecord>(black_box(input)).unwrap());
            }
        })
    });
    group.finish();
}

fn serialize_ber(c: &mut Criterion) {
    let values = values();
    let der = der_inputs(&values);
    let inputs = ber_comprehensive_inputs(&values, &der);
    let vps_values: Vec<_> = inputs
        .iter()
        .map(|x| generated_ber::EVAL_RECORD::Fmt.parse(&&x[..]).unwrap().1)
        .collect();
    let lengths: Vec<_> = vps_values
        .iter()
        .map(|x| generated_ber::EVAL_RECORD::Fmt.prepare(x).unwrap())
        .collect();
    let bytes = lengths.iter().map(|x| *x as u64).sum();
    let mut vps_outputs: Vec<_> = lengths.iter().map(|x| vec![0; *x]).collect();
    let mut rasn_output = Vec::with_capacity(lengths.iter().copied().max().unwrap_or(0));
    let mut group = c.benchmark_group("asn1_ber/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for (value, output) in vps_values.iter().zip(&mut vps_outputs) {
                generated_ber::EVAL_RECORD::Fmt.serialize(value, black_box(output.as_mut_slice()));
                black_box(&output);
            }
        })
    });
    group.bench_function("rasn", |b| {
        b.iter(|| {
            for value in &values {
                rasn::ber::encode_buf(black_box(value), &mut rasn_output).unwrap();
                black_box(&rasn_output);
            }
        })
    });
    group.finish();
}

criterion_group!(benches, parse_der, serialize_der, parse_ber, serialize_ber);
criterion_main!(benches);
