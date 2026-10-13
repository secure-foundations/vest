//! Vest and rust-bitcoin's consensus codecs, using their native value types.

use bitcoin::consensus::{Decodable, Encodable};
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use vest_bench::{harness::Group, real::bitcoin as corpus};
use vest_lib::core::exec::Parser;
use vest_tests::bitcoin::BlockFmt;

fn bench(c: &mut Criterion) {
    let inputs: Vec<_> = corpus::bitcoin_blocks()
        .into_iter()
        .map(|b| b.bytes)
        .collect();
    let values = corpus::values(&inputs);
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    let mut group = Group::new(c, "bitcoin/blocks/parse", inputs.len(), bytes);
    group.retained("Vest", |i| {
        BlockFmt.parse(black_box(&inputs[i].as_slice())).unwrap()
    });
    group.retained("rust-bitcoin", |i| {
        bitcoin::Block::consensus_decode(black_box(&mut &inputs[i][..])).unwrap()
    });
    group.finish();

    let mut output = Vec::with_capacity(inputs.iter().map(Vec::len).max().unwrap());
    let mut group = Group::serializing(c, "bitcoin/blocks/serialize", &BlockFmt, &values.vest);
    group.reused("rust-bitcoin", || {
        for value in &values.bitcoin {
            let n = black_box(value).total_size();
            output.clear();
            output.reserve(n);
            black_box(value)
                .consensus_encode(black_box(&mut output))
                .unwrap();
            black_box(&output);
        }
    });
    group.finish();
}

criterion_group! { name = benches; config = vest_bench::harness::criterion(); targets = bench }
criterion_main!(benches);
