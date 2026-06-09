use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};

use vest_dev::combinators::recursive::FixWith;
use vest_dev::core::exec::parser::Parser;
use vest_dev::core::exec::serializer::{Prepare, Serializer};
use vest_dev::spec_tests::mutual_fix::{
    benchmark_byte_list_values, benchmark_expr_values, benchmark_list_values,
    handrolled_parse_byte_list_checked, handrolled_parse_expr_checked,
    handrolled_parse_list_checked, handrolled_prepare_byte_list_checked,
    handrolled_prepare_expr_checked, handrolled_prepare_list_checked,
    handrolled_serialize_byte_list_checked, handrolled_serialize_expr_checked,
    handrolled_serialize_list_checked, ByteList, ByteListRecBody, Expr, ExprFmt, List, ListFmt,
    BENCH_RECURSION_LIMIT,
};

struct ExprCorpus {
    values: Vec<Expr>,
    encoded: Vec<Vec<u8>>,
    total_bytes: u64,
}

struct ListCorpus {
    values: Vec<List>,
    encoded: Vec<Vec<u8>>,
    total_bytes: u64,
}

struct ByteListCorpus {
    values: Vec<ByteList>,
    encoded: Vec<Vec<u8>>,
    total_bytes: u64,
}

fn make_expr_corpus() -> ExprCorpus {
    let fmt = ExprFmt::<BENCH_RECURSION_LIMIT>;
    let values = benchmark_expr_values();
    let mut encoded = Vec::with_capacity(values.len());
    let mut total_bytes = 0u64;

    for value in &values {
        let prepared_hand =
            handrolled_prepare_expr_checked(value).expect("hand expr prepare failed");
        let mut bytes = Vec::with_capacity(prepared_hand);
        handrolled_serialize_expr_checked(value, &mut bytes).expect("hand expr serialize failed");
        total_bytes += bytes.len() as u64;

        let prepared = fmt.prepare(value).expect("vest expr prepare failed");
        assert_eq!(prepared, bytes.len());
        assert_eq!(prepared_hand, bytes.len());

        let mut vest_bytes = Vec::with_capacity(prepared);
        fmt.serialize(value, &mut vest_bytes);
        assert_eq!(vest_bytes, bytes);

        let (n_vest, parsed_vest) = fmt.parse(&&bytes[..]).expect("vest expr parse failed");
        assert_eq!(n_vest, bytes.len());
        assert_eq!(parsed_vest, *value);

        let (n_hand, parsed_hand) =
            handrolled_parse_expr_checked(&bytes).expect("hand expr parse failed");
        assert_eq!(n_hand, bytes.len());
        assert_eq!(parsed_hand, *value);

        encoded.push(bytes);
    }

    ExprCorpus {
        values,
        encoded,
        total_bytes,
    }
}

fn make_list_corpus() -> ListCorpus {
    let fmt = ListFmt::<BENCH_RECURSION_LIMIT>;
    let values = benchmark_list_values();
    let mut encoded = Vec::with_capacity(values.len());
    let mut total_bytes = 0u64;

    for value in &values {
        let prepared_hand =
            handrolled_prepare_list_checked(value).expect("hand list prepare failed");
        let mut bytes = Vec::with_capacity(prepared_hand);
        handrolled_serialize_list_checked(value, &mut bytes).expect("hand list serialize failed");
        total_bytes += bytes.len() as u64;

        let prepared = fmt.prepare(value).expect("vest list prepare failed");
        assert_eq!(prepared, bytes.len());
        assert_eq!(prepared_hand, bytes.len());

        let mut vest_bytes = Vec::with_capacity(prepared);
        fmt.serialize(value, &mut vest_bytes);
        assert_eq!(vest_bytes, bytes);

        let (n_vest, parsed_vest) = fmt.parse(&&bytes[..]).expect("vest list parse failed");
        assert_eq!(n_vest, bytes.len());
        assert_eq!(parsed_vest, *value);

        let (n_hand, parsed_hand) =
            handrolled_parse_list_checked(&bytes).expect("hand list parse failed");
        assert_eq!(n_hand, bytes.len());
        assert_eq!(parsed_hand, *value);

        encoded.push(bytes);
    }

    ListCorpus {
        values,
        encoded,
        total_bytes,
    }
}

fn make_byte_list_corpus() -> ByteListCorpus {
    let fmt = FixWith::<BENCH_RECURSION_LIMIT, _, _>(ByteListRecBody, ());
    let values = benchmark_byte_list_values();
    let mut encoded = Vec::with_capacity(values.len());
    let mut total_bytes = 0u64;

    for value in &values {
        let prepared_hand =
            handrolled_prepare_byte_list_checked(value).expect("hand byte-list prepare failed");
        let mut bytes = Vec::with_capacity(prepared_hand);
        handrolled_serialize_byte_list_checked(value, &mut bytes)
            .expect("hand byte-list serialize failed");
        total_bytes += bytes.len() as u64;

        let prepared = fmt.prepare(value).expect("vest byte-list prepare failed");
        assert_eq!(prepared, bytes.len());
        assert_eq!(prepared_hand, bytes.len());

        let mut vest_bytes = Vec::with_capacity(prepared);
        fmt.serialize(value, &mut vest_bytes);
        assert_eq!(vest_bytes, bytes);

        let (n_vest, parsed_vest) = fmt.parse(&&bytes[..]).expect("vest byte-list parse failed");
        assert_eq!(n_vest, bytes.len());
        assert_eq!(parsed_vest, *value);

        let (n_hand, parsed_hand) =
            handrolled_parse_byte_list_checked(&bytes).expect("hand byte-list parse failed");
        assert_eq!(n_hand, bytes.len());
        assert_eq!(parsed_hand, *value);

        encoded.push(bytes);
    }

    ByteListCorpus {
        values,
        encoded,
        total_bytes,
    }
}

fn bench_expr_parse_bulk(c: &mut Criterion) {
    let corpus = make_expr_corpus();
    let fmt = ExprFmt::<BENCH_RECURSION_LIMIT>;

    let mut group = c.benchmark_group("mutual_fix_expr_parse");
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
                let parsed = handrolled_parse_expr_checked(black_box(&bytes[..])).unwrap();
                black_box(parsed);
            }
        })
    });

    group.finish();
}

fn bench_list_parse_bulk(c: &mut Criterion) {
    let corpus = make_list_corpus();
    let fmt = ListFmt::<BENCH_RECURSION_LIMIT>;

    let mut group = c.benchmark_group("mutual_fix_list_parse");
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
                let parsed = handrolled_parse_list_checked(black_box(&bytes[..])).unwrap();
                black_box(parsed);
            }
        })
    });

    group.finish();
}

fn bench_expr_serialize_bulk(c: &mut Criterion) {
    let corpus = make_expr_corpus();
    let fmt = ExprFmt::<BENCH_RECURSION_LIMIT>;

    let mut group = c.benchmark_group("mutual_fix_expr_serialize");
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
                handrolled_serialize_expr_checked(black_box(value), &mut out).unwrap();
                black_box(out);
            }
        })
    });

    group.finish();
}

fn bench_list_serialize_bulk(c: &mut Criterion) {
    let corpus = make_list_corpus();
    let fmt = ListFmt::<BENCH_RECURSION_LIMIT>;

    let mut group = c.benchmark_group("mutual_fix_list_serialize");
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
                handrolled_serialize_list_checked(black_box(value), &mut out).unwrap();
                black_box(out);
            }
        })
    });

    group.finish();
}

fn bench_byte_list_parse_bulk(c: &mut Criterion) {
    let corpus = make_byte_list_corpus();
    let fmt = FixWith::<BENCH_RECURSION_LIMIT, _, _>(ByteListRecBody, ());

    let mut group = c.benchmark_group("self_fix_byte_list_parse");
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
                let parsed = handrolled_parse_byte_list_checked(black_box(&bytes[..])).unwrap();
                black_box(parsed);
            }
        })
    });

    group.finish();
}

fn bench_byte_list_serialize_bulk(c: &mut Criterion) {
    let corpus = make_byte_list_corpus();
    let fmt = FixWith::<BENCH_RECURSION_LIMIT, _, _>(ByteListRecBody, ());

    let mut group = c.benchmark_group("self_fix_byte_list_serialize");
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
                handrolled_serialize_byte_list_checked(black_box(value), &mut out).unwrap();
                black_box(out);
            }
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_expr_parse_bulk,
    bench_list_parse_bulk,
    bench_expr_serialize_bulk,
    bench_list_serialize_bulk,
    bench_byte_list_parse_bulk,
    bench_byte_list_serialize_bulk,
);
criterion_main!(benches);
