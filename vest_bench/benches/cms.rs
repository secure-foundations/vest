//! CMS benchmarks over a synthetic ContentInfo workload and three public corpora.

use std::hint::black_box;

use bcder::{encode::Values, Mode};
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use der::{Decode, Encode};
use vest_asn1_tests::generated_cms;
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

#[path = "shared/cms.rs"]
mod checks;
#[path = "shared/timing.rs"]
mod harness;

use checks::{econtent_body, parse_bcder, real_signed_data, synthetic_content_info};

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
        let rasn_value: rasn_cms::ContentInfo = checks::rasn_exact(input);
        let rustcrypto = rustcrypto_cms::content_info::ContentInfo::from_ber(input).unwrap();
        let bcder = parse_bcder(input);
        assert_eq!(rasn::der::encode(&rasn_value).unwrap(), *input);
        assert_eq!(rustcrypto.to_der().unwrap(), *input);
        assert_eq!(
            checks::bcder_content_info(&bcder)
                .to_captured(Mode::Der)
                .as_slice(),
            &input[..]
        );
        let value = generated_cms::CONTENT_INFO::Fmt
            .parse(&&input[..])
            .unwrap()
            .1;
        let mut output = vec![0; generated_cms::CONTENT_INFO::Fmt.prepare(&value).unwrap()];
        generated_cms::CONTENT_INFO::Fmt.serialize(&value, &mut output);
        assert_eq!(output, *input);
    }
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    harness::corpus_metadata("cms/content_info/parse", inputs.len(), bytes);
    let mut group = c.benchmark_group("cms/content_info/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        harness::retained(b, inputs.len(), |i| {
            generated_cms::CONTENT_INFO::Fmt
                .parse(black_box(&&inputs[i][..]))
                .unwrap()
        })
    });
    group.bench_function("rasn-cms", |b| {
        harness::retained(b, inputs.len(), |i| {
            rasn::ber::decode::<rasn_cms::ContentInfo>(black_box(&inputs[i])).unwrap()
        })
    });
    group.bench_function("RustCrypto-cms", |b| {
        harness::retained(b, inputs.len(), |i| {
            rustcrypto_cms::content_info::ContentInfo::from_ber(black_box(&inputs[i])).unwrap()
        })
    });
    group.bench_function("cryptographic-message-syntax", |b| {
        harness::retained(b, inputs.len(), |i| parse_bcder(black_box(&inputs[i])))
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
    harness::corpus_metadata("cms/content_info/serialize", inputs.len(), bytes);
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut vest_output = vec![0; capacity];
    let mut rasn_output = Vec::with_capacity(capacity);
    let mut rustcrypto_output = vec![0; capacity];
    let mut bcder_output = Vec::with_capacity(capacity);
    for ((((value, rasn), rustcrypto), bcder), input) in vest_values
        .iter()
        .zip(&rasn_values)
        .zip(&rustcrypto_values)
        .zip(&bcder_values)
        .zip(&inputs)
    {
        let n = generated_cms::CONTENT_INFO::Fmt.prepare(value).unwrap();
        generated_cms::CONTENT_INFO::Fmt.serialize(value, &mut vest_output[..n]);
        assert_eq!(&vest_output[..n], &input[..]);
        rasn::der::encode_buf(rasn, &mut rasn_output).unwrap();
        assert_eq!(&rasn_output, input);
        assert_eq!(
            rustcrypto.encode_to_slice(&mut rustcrypto_output).unwrap(),
            &input[..]
        );
        bcder_output.clear();
        checks::bcder_content_info(bcder)
            .write_encoded(Mode::Der, &mut bcder_output)
            .unwrap();
        assert_eq!(&bcder_output, input);
    }
    let mut group = c.benchmark_group("cms/content_info/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        harness::reused(b, || {
            for value in &vest_values {
                let n = generated_cms::CONTENT_INFO::Fmt
                    .prepare(black_box(value))
                    .unwrap();
                generated_cms::CONTENT_INFO::Fmt
                    .serialize(black_box(value), black_box(&mut vest_output[..n]));
                black_box(&vest_output[..n]);
            }
        })
    });
    group.bench_function("rasn-cms", |b| {
        harness::retained(b, rasn_values.len(), |i| {
            rasn::der::encode(black_box(&rasn_values[i])).unwrap()
        })
    });
    group.bench_function("RustCrypto-cms", |b| {
        harness::reused(b, || {
            for value in &rustcrypto_values {
                let n = usize::try_from(black_box(value).encoded_len().unwrap()).unwrap();
                black_box(value.encode_to_slice(&mut rustcrypto_output[..n]).unwrap());
            }
        })
    });
    group.bench_function("cryptographic-message-syntax", |b| {
        harness::reused(b, || {
            for value in &bcder_values {
                let encoded = checks::bcder_content_info(black_box(value));
                let n = encoded.encoded_len(Mode::Der);
                bcder_output.clear();
                bcder_output.reserve(n);
                encoded.write_encoded(Mode::Der, &mut bcder_output).unwrap();
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
        let expected = checks::normalized_signed_data(input);
        let value = generated_cms::SIGNED_DATA::Fmt
            .parse(&&input[..])
            .unwrap()
            .1;
        let mut output = vec![0; generated_cms::SIGNED_DATA::Fmt.prepare(&value).unwrap()];
        generated_cms::SIGNED_DATA::Fmt.serialize(&value, &mut output);
        assert_eq!(checks::normalized_signed_data(&output), expected);
        let mut rustcrypto = rustcrypto_cms::signed_data::SignedData::from_ber(input).unwrap();
        assert!(
            rustcrypto
                .encap_content_info
                .econtent
                .as_ref()
                .map(|value| value.value())
                == econtent_body(input),
            "RustCrypto changed raw eContent bytes"
        );
        // Compare all remaining fields under the common encoding as well.
        // ANY loses the constructed bit, so flattening after re-encoding would
        // mistake chunk headers for application content. Check raw preservation
        // above before replacing this field with the independently decoded value.
        let rasn: rasn_cms::SignedData = checks::rasn_exact(input);
        rustcrypto.encap_content_info.econtent = rasn
            .encap_content_info
            .content
            .map(|bytes| der::asn1::Any::new(der::Tag::OctetString, bytes.to_vec()).unwrap());
        assert!(
            checks::normalized_signed_data(&rustcrypto.to_der().unwrap()) == expected,
            "RustCrypto changed SignedData fields"
        );
    }
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    harness::corpus_metadata("cms/real_signed_data/parse", inputs.len(), bytes);
    let mut group = c.benchmark_group("cms/real_signed_data/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        harness::retained(b, inputs.len(), |i| {
            generated_cms::SIGNED_DATA::Fmt
                .parse(black_box(&&inputs[i][..]))
                .unwrap()
        })
    });
    group.bench_function("rasn-cms", |b| {
        harness::retained(b, inputs.len(), |i| {
            rasn::ber::decode::<rasn_cms::SignedData>(black_box(&inputs[i])).unwrap()
        })
    });
    group.bench_function("RustCrypto-cms", |b| {
        harness::retained(b, inputs.len(), |i| {
            rustcrypto_cms::signed_data::SignedData::from_ber(black_box(&inputs[i])).unwrap()
        })
    });
    group.finish();
}

fn real_serialize(c: &mut Criterion) {
    let original = real_signed_data();
    let inputs: Vec<_> = original
        .iter()
        .map(|input| checks::normalized_signed_data(input))
        .collect();
    assert_eq!(inputs.len(), original.len());
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
    harness::corpus_metadata("cms/real_signed_data/serialize", inputs.len(), bytes);
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut vest_output = vec![0; capacity];
    let mut rasn_output = Vec::with_capacity(capacity);
    let mut rustcrypto_output = vec![0; capacity];
    for (((value, rasn), rustcrypto), input) in vest_values
        .iter()
        .zip(&rasn_values)
        .zip(&rustcrypto_values)
        .zip(&inputs)
    {
        let n = generated_cms::SIGNED_DATA::Fmt.prepare(value).unwrap();
        assert_eq!(n, input.len());
        generated_cms::SIGNED_DATA::Fmt.serialize(value, &mut vest_output[..n]);
        assert_eq!(&vest_output[..n], &input[..]);
        rasn::der::encode_buf(rasn, &mut rasn_output).unwrap();
        assert_eq!(&rasn_output, input);
        assert_eq!(
            rustcrypto.encode_to_slice(&mut rustcrypto_output).unwrap(),
            &input[..]
        );
    }
    let mut group = c.benchmark_group("cms/real_signed_data/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        harness::reused(b, || {
            for value in &vest_values {
                let n = generated_cms::SIGNED_DATA::Fmt
                    .prepare(black_box(value))
                    .unwrap();
                generated_cms::SIGNED_DATA::Fmt
                    .serialize(black_box(value), black_box(&mut vest_output[..n]));
                black_box(&vest_output[..n]);
            }
        })
    });
    group.bench_function("rasn-cms", |b| {
        harness::retained(b, rasn_values.len(), |i| {
            rasn::der::encode(black_box(&rasn_values[i])).unwrap()
        })
    });
    group.bench_function("RustCrypto-cms", |b| {
        harness::reused(b, || {
            for value in &rustcrypto_values {
                let n = usize::try_from(black_box(value).encoded_len().unwrap()).unwrap();
                black_box(value.encode_to_slice(&mut rustcrypto_output[..n]).unwrap());
            }
        })
    });
    group.finish();
}

criterion_group! { name = benches; config = harness::configuration();
targets = synthetic, synthetic_serialize, real_parse, real_serialize }
criterion_main!(benches);
