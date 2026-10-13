//! CMS codecs over synthetic ContentInfo and original/normalized SignedData.
use bcder::{encode::Values, Mode};
use criterion::{criterion_group, criterion_main, Criterion};
use der::{Decode, Encode};
use std::hint::black_box;
use vest_bench::{harness::Group, real::cms};
use vest_lib::core::exec::Parser;

fn synthetic(c: &mut Criterion) {
    let inputs = cms::synthetic_content_info();
    let values = cms::content_info_values(&inputs);
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    let mut group = Group::new(c, "cms/content_info/parse", inputs.len(), bytes);
    group.retained("Vest", |i| {
        cms::CONTENT_INFO
            .parse(black_box(&inputs[i].as_slice()))
            .unwrap()
    });
    group.retained("rasn-cms", |i| {
        rasn::ber::decode::<rasn_cms::ContentInfo>(black_box(&inputs[i])).unwrap()
    });
    group.retained("RustCrypto-cms", |i| {
        rustcrypto_cms::content_info::ContentInfo::from_ber(black_box(&inputs[i])).unwrap()
    });
    group.retained("cryptographic-message-syntax", |i| {
        cms::parse_bcder(black_box(&inputs[i]))
    });
    group.finish();

    let capacity = inputs.iter().map(Vec::len).max().unwrap();
    let mut rustcrypto_output = vec![0; capacity];
    let mut bcder_output = Vec::with_capacity(capacity);
    let mut group = Group::serializing(
        c,
        "cms/content_info/serialize",
        &cms::CONTENT_INFO,
        &values.vest,
    );
    group.retained("rasn-cms", |i| {
        rasn::der::encode(black_box(&values.rasn[i])).unwrap()
    });
    group.reused("RustCrypto-cms", || {
        for value in &values.rustcrypto {
            let n = usize::try_from(black_box(value).encoded_len().unwrap()).unwrap();
            black_box(value.encode_to_slice(&mut rustcrypto_output[..n]).unwrap());
        }
    });
    group.reused("cryptographic-message-syntax", || {
        for value in &values.bcder {
            let encoded = cms::bcder_content_info(black_box(value));
            let n = encoded.encoded_len(Mode::Der);
            bcder_output.clear();
            bcder_output.reserve(n);
            encoded.write_encoded(Mode::Der, &mut bcder_output).unwrap();
            black_box(&bcder_output);
        }
    });
    group.finish();
}

fn real(c: &mut Criterion) {
    let inputs = cms::real_signed_data();
    let common = cms::validated_signed_data(&inputs);
    let values = cms::signed_data_values(&common);
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    let mut group = Group::new(c, "cms/real_signed_data/parse", inputs.len(), bytes);
    group.retained("Vest", |i| {
        cms::SIGNED_DATA
            .parse(black_box(&inputs[i].as_slice()))
            .unwrap()
    });
    group.retained("rasn-cms", |i| {
        rasn::ber::decode::<rasn_cms::SignedData>(black_box(&inputs[i])).unwrap()
    });
    group.retained("RustCrypto-cms", |i| {
        rustcrypto_cms::signed_data::SignedData::from_ber(black_box(&inputs[i])).unwrap()
    });
    group.finish();

    let mut output = vec![0; common.iter().map(Vec::len).max().unwrap()];
    let mut group = Group::serializing(
        c,
        "cms/real_signed_data/serialize",
        &cms::SIGNED_DATA,
        &values.vest,
    );
    group.retained("rasn-cms", |i| {
        rasn::der::encode(black_box(&values.rasn[i])).unwrap()
    });
    group.reused("RustCrypto-cms", || {
        for value in &values.rustcrypto {
            let n = usize::try_from(black_box(value).encoded_len().unwrap()).unwrap();
            black_box(value.encode_to_slice(&mut output[..n]).unwrap());
        }
    });
    group.finish();
}

criterion_group! { name = benches; config = vest_bench::harness::criterion(); targets = synthetic, real }
criterion_main!(benches);
