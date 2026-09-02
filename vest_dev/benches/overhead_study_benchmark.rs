/// Benchmark for overhead isolation experiment.
///
/// Three variants per operation (parse / serialize / prepare):
///   A. handrolled       — direct mutual recursion, typed pointers, no wrapping
///   B. handrolled_tagged — same logic but wraps into TaggedValue enum (mirrors ValueRef)
///   C. vest_fixwith     — FixWith combinator with TreeNodeValueRef
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use vest_dev::combinators::recursive::FixWith;
use vest_dev::core::exec::parser::Parser;
use vest_dev::core::exec::serializer::Prepare;
use vest_dev::core::exec::SerializerExt;
use vest_dev::formats::overhead_study::{
    benchmark_tree_values, handrolled_parse_tree, handrolled_prepare_tree,
    handrolled_serialize_tree, handrolled_tagged_parse_tree, handrolled_tagged_prepare_tree,
    handrolled_tagged_serialize_tree, Tree, TreeNodeRecBody, TreeNodeValueRef, WhichFmt,
    BENCH_RECURSION_LIMIT,
};

struct Corpus {
    values: Vec<Tree>,
    encoded: Vec<Vec<u8>>,
    total_bytes: u64,
}

fn make_corpus() -> Corpus {
    let fmt = FixWith::<BENCH_RECURSION_LIMIT, _, _>(TreeNodeRecBody, WhichFmt::TREE);
    let values = benchmark_tree_values();
    let mut encoded = Vec::with_capacity(values.len());
    let mut total_bytes = 0u64;

    for value in &values {
        // Use handrolled A as the ground-truth encoder for the corpus
        let mut bytes = Vec::new();
        handrolled_serialize_tree(value, &mut bytes).expect("A: serialize failed");
        total_bytes += bytes.len() as u64;

        // Cross-check all three variants agree on the encoding
        let prepared_a = handrolled_prepare_tree(value).expect("A: prepare failed");
        assert_eq!(prepared_a, bytes.len(), "A prepare mismatch");

        let prepared_b = handrolled_tagged_prepare_tree(value).expect("B: prepare failed");
        assert_eq!(prepared_b, bytes.len(), "B prepare mismatch");

        let vr = TreeNodeValueRef::IsTree { tree: value };
        let prepared_c = fmt.prepare(&vr).expect("C: prepare failed");
        assert_eq!(prepared_c, bytes.len(), "C prepare mismatch");

        let mut b_bytes = Vec::with_capacity(bytes.len());
        handrolled_tagged_serialize_tree(value, &mut b_bytes).expect("B: serialize failed");
        assert_eq!(b_bytes, bytes, "B/A encoding mismatch");

        let mut c_bytes = vec![0; prepared_c];
        fmt.serialize(&vr, &mut c_bytes);
        assert_eq!(c_bytes, bytes, "C/A encoding mismatch");

        let (na, va) = handrolled_parse_tree(&bytes).expect("A: parse failed");
        assert_eq!(na, bytes.len());
        assert_eq!(va, *value);

        let (nb, vb) = handrolled_tagged_parse_tree(&bytes).expect("B: parse failed");
        assert_eq!(nb, bytes.len());
        assert_eq!(vb, *value);

        let (nc, inner) = fmt.parse(&&bytes[..]).expect("C: parse failed");
        assert_eq!(nc, bytes.len());
        match inner {
            vest_dev::formats::overhead_study::TreeNodeValue::IsTree { tree: t } => {
                assert_eq!(t, *value)
            }
            _ => panic!("unexpected variant"),
        }

        encoded.push(bytes);
    }

    Corpus {
        values,
        encoded,
        total_bytes,
    }
}

// ── Parse benchmarks ──────────────────────────────────────────────────────────

fn bench_parse(c: &mut Criterion) {
    let corpus = make_corpus();
    let fmt = FixWith::<BENCH_RECURSION_LIMIT, _, _>(TreeNodeRecBody, WhichFmt::TREE);

    let mut g = c.benchmark_group("tree_parse");
    g.throughput(Throughput::Bytes(corpus.total_bytes));

    g.bench_function("A_handrolled", |b| {
        b.iter(|| {
            for bytes in &corpus.encoded {
                black_box(handrolled_parse_tree(black_box(&bytes[..])).unwrap());
            }
        })
    });

    g.bench_function("B_tagged", |b| {
        b.iter(|| {
            for bytes in &corpus.encoded {
                black_box(handrolled_tagged_parse_tree(black_box(&bytes[..])).unwrap());
            }
        })
    });

    g.bench_function("C_vest_fixwith", |b| {
        b.iter(|| {
            for bytes in &corpus.encoded {
                black_box(fmt.parse(black_box(&&bytes[..])).unwrap());
            }
        })
    });

    g.finish();
}

// ── Serialize benchmarks ──────────────────────────────────────────────────────

fn bench_serialize(c: &mut Criterion) {
    let corpus = make_corpus();
    let fmt = FixWith::<BENCH_RECURSION_LIMIT, _, _>(TreeNodeRecBody, WhichFmt::TREE);

    let mut g = c.benchmark_group("tree_serialize");
    g.throughput(Throughput::Bytes(corpus.total_bytes));

    g.bench_function("A_handrolled", |b| {
        b.iter(|| {
            for (value, bytes) in corpus.values.iter().zip(&corpus.encoded) {
                let mut out = Vec::with_capacity(bytes.len());
                handrolled_serialize_tree(black_box(value), &mut out).unwrap();
                black_box(out);
            }
        })
    });

    g.bench_function("B_tagged", |b| {
        b.iter(|| {
            for (value, bytes) in corpus.values.iter().zip(&corpus.encoded) {
                let mut out = Vec::with_capacity(bytes.len());
                handrolled_tagged_serialize_tree(black_box(value), &mut out).unwrap();
                black_box(out);
            }
        })
    });

    g.bench_function("C_vest_fixwith", |b| {
        b.iter(|| {
            for (value, bytes) in corpus.values.iter().zip(&corpus.encoded) {
                let vr = TreeNodeValueRef::IsTree {
                    tree: black_box(value),
                };
                let mut out = Vec::with_capacity(bytes.len());
                fmt.serialize(&vr, &mut out);
                black_box(out);
            }
        })
    });

    g.finish();
}

// ── Prepare benchmarks ────────────────────────────────────────────────────────

fn bench_prepare(c: &mut Criterion) {
    let corpus = make_corpus();
    let fmt = FixWith::<BENCH_RECURSION_LIMIT, _, _>(TreeNodeRecBody, WhichFmt::TREE);

    let mut g = c.benchmark_group("tree_prepare");

    g.bench_function("A_handrolled", |b| {
        b.iter(|| {
            for value in &corpus.values {
                black_box(handrolled_prepare_tree(black_box(value)).unwrap());
            }
        })
    });

    g.bench_function("B_tagged", |b| {
        b.iter(|| {
            for value in &corpus.values {
                black_box(handrolled_tagged_prepare_tree(black_box(value)).unwrap());
            }
        })
    });

    g.bench_function("C_vest_fixwith", |b| {
        b.iter(|| {
            for value in &corpus.values {
                let vr = TreeNodeValueRef::IsTree {
                    tree: black_box(value),
                };
                black_box(fmt.prepare(&vr).unwrap());
            }
        })
    });

    g.finish();
}

criterion_group!(benches, bench_parse, bench_serialize, bench_prepare);
criterion_main!(benches);
