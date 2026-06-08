use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};

use vest_dev::combinators::recursive::FixWith;
use vest_dev::core::exec::parser::Parser;
use vest_dev::core::exec::serializer::{Prepare, Serializer};
use vest_dev::spec_tests::fix::{
    benchmark_nested_braces_values, handrolled_parse_nested_braces_checked,
    handrolled_prepare_nested_braces_checked, handrolled_serialize_nested_braces_checked,
    NestedBracesBody, NestedBracesT, NESTED_BRACES_BENCH_LIMIT,
};

struct NestedBracesCorpus {
    values: Vec<NestedBracesT>,
    encoded: Vec<Vec<u8>>,
    total_bytes: u64,
}

fn make_corpus() -> NestedBracesCorpus {
    let fmt = FixWith::<NESTED_BRACES_BENCH_LIMIT, _, _>(NestedBracesBody, ());
    let values = benchmark_nested_braces_values();
    let mut encoded = Vec::with_capacity(values.len());
    let mut total_bytes = 0u64;

    for value in &values {
        let prepared_hand =
            handrolled_prepare_nested_braces_checked(value).expect("hand prepare failed");
        let mut bytes = Vec::with_capacity(prepared_hand);
        handrolled_serialize_nested_braces_checked(value, &mut bytes)
            .expect("hand serialize failed");
        total_bytes += bytes.len() as u64;

        let prepared_vest = fmt.prepare(value).expect("vest prepare failed");
        assert_eq!(prepared_vest, bytes.len());
        assert_eq!(prepared_hand, bytes.len());

        let mut vest_bytes = Vec::with_capacity(prepared_vest);
        fmt.serialize(value, &mut vest_bytes);
        assert_eq!(vest_bytes, bytes);

        let (n_vest, parsed_vest) = fmt.parse(&&bytes[..]).expect("vest parse failed");
        assert_eq!(n_vest, bytes.len());
        let mut vest_roundtrip = Vec::with_capacity(bytes.len());
        fmt.serialize(&parsed_vest, &mut vest_roundtrip);
        assert_eq!(vest_roundtrip, bytes);

        let (n_hand, parsed_hand) =
            handrolled_parse_nested_braces_checked(&bytes).expect("hand parse failed");
        assert_eq!(n_hand, bytes.len());
        let mut hand_roundtrip = Vec::with_capacity(bytes.len());
        handrolled_serialize_nested_braces_checked(&parsed_hand, &mut hand_roundtrip)
            .expect("hand roundtrip serialize failed");
        assert_eq!(hand_roundtrip, bytes);

        encoded.push(bytes);
    }

    NestedBracesCorpus {
        values,
        encoded,
        total_bytes,
    }
}

fn bench_nested_braces_parse_bulk(c: &mut Criterion) {
    let corpus = make_corpus();
    let fmt = FixWith::<NESTED_BRACES_BENCH_LIMIT, _, _>(NestedBracesBody, ());

    let mut group = c.benchmark_group("nested_braces_parse");
    group.throughput(Throughput::Bytes(corpus.total_bytes));

    group.bench_function("vest_fixwith_bulk", |b| {
        b.iter(|| {
            for bytes in &corpus.encoded {
                let input = black_box(&bytes[..]);
                let parsed = fmt.parse(&input).unwrap();
                black_box(parsed);
            }
        })
    });

    group.bench_function("handrolled_bulk", |b| {
        b.iter(|| {
            for bytes in &corpus.encoded {
                let parsed = handrolled_parse_nested_braces_checked(black_box(&bytes[..])).unwrap();
                black_box(parsed);
            }
        })
    });

    group.finish();
}

fn bench_nested_braces_serialize_bulk(c: &mut Criterion) {
    let corpus = make_corpus();
    let fmt = FixWith::<NESTED_BRACES_BENCH_LIMIT, _, _>(NestedBracesBody, ());

    let mut group = c.benchmark_group("nested_braces_serialize");
    group.throughput(Throughput::Bytes(corpus.total_bytes));

    group.bench_function("vest_fixwith_bulk", |b| {
        b.iter(|| {
            for (value, bytes) in corpus.values.iter().zip(&corpus.encoded) {
                let mut out = Vec::with_capacity(bytes.len());
                fmt.serialize(black_box(value), &mut out);
                black_box(out);
            }
        })
    });

    group.bench_function("handrolled_bulk", |b| {
        b.iter(|| {
            for (value, bytes) in corpus.values.iter().zip(&corpus.encoded) {
                let mut out = Vec::with_capacity(bytes.len());
                handrolled_serialize_nested_braces_checked(black_box(value), &mut out).unwrap();
                black_box(out);
            }
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_nested_braces_parse_bulk,
    bench_nested_braces_serialize_bulk,
);
criterion_main!(benches);
