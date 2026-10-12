//! Vest's Bitcoin codec compared with the `bitcoin` crate's consensus codec.
//!
//! Unlike the microbenchmarks in `formats.rs`, each implementation uses its
//! native Rust value type.

use std::fs::File;
use std::hint::black_box;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

use base64::prelude::*;
use bitcoin::consensus::{Decodable, Encodable};
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use vest_bench::corpora;
use vest_lib::core::exec::parser::Parser;
use vest_lib::core::exec::serializer::{Prepare, SerializerExt};
use vest_tests::bitcoin::BlockFmt;

#[path = "shared/timing.rs"]
mod harness;

/// The checked-in mainnet blocks, or the external corpus named by
/// `VEST_BENCH_BITCOIN_CORPUS`: one base64-encoded block per line.
fn blocks() -> Vec<Vec<u8>> {
    let Some(path) = std::env::var_os("VEST_BENCH_BITCOIN_CORPUS") else {
        return corpora::bitcoin_blocks()
            .into_iter()
            .map(|block| block.bytes)
            .collect();
    };
    BufReader::new(File::open(PathBuf::from(path)).expect("open Bitcoin corpus"))
        .lines()
        .map(|line| BASE64_STANDARD.decode(line.unwrap()).unwrap())
        .collect()
}

fn parse(c: &mut Criterion) {
    let inputs = blocks();
    for input in &inputs {
        let (n, value) = BlockFmt.parse(&&input[..]).unwrap();
        assert_eq!(n, input.len());
        let mut remaining = &input[..];
        let baseline = bitcoin::Block::consensus_decode(&mut remaining).unwrap();
        assert!(remaining.is_empty());
        let mut encoded = vec![0; BlockFmt.prepare(&value).unwrap()];
        BlockFmt.serialize(&value, &mut encoded);
        assert_eq!(&encoded, input);
        encoded.clear();
        baseline.consensus_encode(&mut encoded).unwrap();
        assert_eq!(&encoded, input);
    }
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    harness::corpus_metadata("bitcoin/parse", inputs.len(), bytes);
    let mut group = c.benchmark_group("bitcoin/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        harness::retained(b, inputs.len(), |i| {
            BlockFmt.parse(black_box(&&inputs[i][..])).unwrap()
        })
    });
    group.bench_function("rust-bitcoin", |b| {
        harness::retained(b, inputs.len(), |i| {
            bitcoin::Block::consensus_decode(black_box(&mut &inputs[i][..])).unwrap()
        })
    });
    group.finish();
}

fn serialize(c: &mut Criterion) {
    let inputs = blocks();
    let vest_values: Vec<_> = inputs
        .iter()
        .map(|input| BlockFmt.parse(&&input[..]).unwrap().1)
        .collect();
    let baseline_values: Vec<_> = inputs
        .iter()
        .map(|input| bitcoin::Block::consensus_decode(&mut &input[..]).unwrap())
        .collect();
    let lengths: Vec<_> = vest_values
        .iter()
        .map(|value| BlockFmt.prepare(value).unwrap())
        .collect();
    let bytes = lengths.iter().map(|length| *length as u64).sum();
    harness::corpus_metadata("bitcoin/serialize", inputs.len(), bytes);
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut vest_output = vec![0; capacity];
    let mut baseline_output = Vec::with_capacity(capacity);
    for ((value, baseline), input) in vest_values.iter().zip(&baseline_values).zip(&inputs) {
        let n = BlockFmt.prepare(value).unwrap();
        BlockFmt.serialize(value, &mut vest_output[..n]);
        assert_eq!(&vest_output[..n], &input[..]);
        baseline_output.clear();
        assert_eq!(baseline.total_size(), input.len());
        baseline.consensus_encode(&mut baseline_output).unwrap();
        assert_eq!(&baseline_output, input);
    }
    let mut group = c.benchmark_group("bitcoin/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        harness::reused(b, || {
            for value in &vest_values {
                let n = BlockFmt.prepare(black_box(value)).unwrap();
                BlockFmt.serialize(black_box(value), black_box(&mut vest_output[..n]));
                black_box(&vest_output[..n]);
            }
        })
    });
    group.bench_function("rust-bitcoin", |b| {
        harness::reused(b, || {
            for value in &baseline_values {
                let n = black_box(value).total_size();
                baseline_output.clear();
                baseline_output.reserve(n);
                black_box(value)
                    .consensus_encode(black_box(&mut baseline_output))
                    .unwrap();
                black_box(&baseline_output);
            }
        })
    });
    group.finish();
}

criterion_group! { name = benches; config = harness::configuration(); targets = parse, serialize }
criterion_main!(benches);
