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
use vest_bench::real;
use vest_lib::core::exec::parser::Parser;
use vest_lib::core::exec::serializer::{Prepare, SerializerExt};
use vest_tests::bitcoin::BlockFmt;

/// The checked-in mainnet blocks, or the external corpus named by
/// `VEST_BENCH_BITCOIN_CORPUS`: one base64-encoded block per line.
fn blocks() -> Vec<Vec<u8>> {
    let Some(path) = std::env::var_os("VEST_BENCH_BITCOIN_CORPUS") else {
        return real::bitcoin_blocks()
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
    let mut group = c.benchmark_group("bitcoin/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(BlockFmt.parse(black_box(&&input[..])).unwrap());
            }
        })
    });
    group.bench_function("rust-bitcoin", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(bitcoin::Block::consensus_decode(black_box(&mut &input[..])).unwrap());
            }
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
    let capacity = lengths.iter().copied().max().unwrap_or(0);
    let mut vest_output = vec![0; capacity];
    let mut baseline_output = Vec::with_capacity(capacity);
    for ((value, baseline), input) in vest_values.iter().zip(&baseline_values).zip(&inputs) {
        let n = BlockFmt.prepare(value).unwrap();
        BlockFmt.serialize(value, &mut vest_output[..n]);
        assert_eq!(&vest_output[..n], &input[..]);
        baseline_output.clear();
        baseline.consensus_encode(&mut baseline_output).unwrap();
        assert_eq!(&baseline_output, input);
    }
    let mut group = c.benchmark_group("bitcoin/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for (value, length) in vest_values.iter().zip(&lengths) {
                BlockFmt.serialize(black_box(value), black_box(&mut vest_output[..*length]));
                black_box(&vest_output[..*length]);
            }
        })
    });
    group.bench_function("rust-bitcoin", |b| {
        b.iter(|| {
            for value in &baseline_values {
                baseline_output.clear();
                black_box(value)
                    .consensus_encode(black_box(&mut baseline_output))
                    .unwrap();
                black_box(&baseline_output);
            }
        })
    });
    group.finish();
}

criterion_group!(benches, parse, serialize);
criterion_main!(benches);
