#![allow(unused)]

extern crate bitcoin;
extern crate vestbitcoin;

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use std::time::Duration;

use criterion::Throughput;
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};

use vest::properties::Combinator;
use vestbitcoin::vest_bitcoin::*;

use bitcoin::consensus::{Decodable, Encodable};

use base64::prelude::*;

/// Load blocks stored in benches/data/sampled_blocks.txt
fn load_bitcoin_blocks(path: &str) -> Vec<Vec<u8>> {
    let mut blocks_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    blocks_path.push(path);
    let blocks_file = File::open(blocks_path).expect("failed to read blocks data");

    BufReader::new(blocks_file)
        .lines()
        .map(|line| {
            BASE64_STANDARD
                .decode(line.unwrap())
                .expect("failed to load test blocks")
        })
        .collect::<Vec<_>>()
}

/// Benchmark parsing time of 1K bitcoin blocks
fn bench_parse_bitcoin_1k_blocks_bulk(c: &mut Criterion) {
    let test_blocks = load_bitcoin_blocks("benches/data/sampled_blocks.txt");

    let mut group = c.benchmark_group("parse_bitcoin_1k_blocks_bulk");
    group.bench_function("vest", |b| {
        b.iter(|| {
            for block_bytes in test_blocks.iter() {
                parse_block(black_box(block_bytes)).unwrap();
            }
        })
    });
    group.bench_function("rust_bitcoin", |b| {
        b.iter(|| {
            for block_bytes in test_blocks.iter() {
                bitcoin::Block::consensus_decode(&mut &block_bytes[..]).unwrap();
            }
        })
    });
    group.finish();
}

/// Benchmark parsing 1K bitcoin blocks, but collect data on each block
fn bench_parse_bitcoin_1k_blocks(c: &mut Criterion) {
    let test_blocks = load_bitcoin_blocks("benches/data/sampled_blocks.txt");

    let mut group = c.benchmark_group("parse_bitcoin_1k_blocks");
    group.sample_size(20);
    group.warm_up_time(Duration::from_millis(100));
    group.measurement_time(Duration::from_millis(200));

    for (i, test_block) in test_blocks.iter().enumerate() {
        group.bench_function(format!("vest_{}", i), |b| {
            b.iter(|| parse_block(black_box(test_block)).unwrap())
        });
        group.bench_function(format!("rust_bitcoin_{}", i), |b| {
            b.iter(|| bitcoin::Block::consensus_decode(&mut &test_block[..]).unwrap())
        });
    }

    group.finish();
}

/// Benchmark serializing 1K bitcoin blocks
fn bench_serialize_bitcoin_1k_blocks_bulk(c: &mut Criterion) {
    let test_blocks = load_bitcoin_blocks("benches/data/sampled_blocks.txt");

    // Get the largest block size
    let max_block_size = test_blocks.iter().map(|block| block.len()).max().unwrap();

    let mut group = c.benchmark_group("serialize_bitcoin_1k_blocks_bulk");
    group.sample_size(10);

    group.bench_function("vest", |b| {
        b.iter_batched_ref(
            || {
                test_blocks
                    .iter()
                    .map(|b| parse_block(b).unwrap().1)
                    .collect::<Vec<_>>()
            },
            |vest_parsed| {
                for b in vest_parsed {
                    let mut buf = vec![0; max_block_size];
                    serialize_block(b, &mut buf, 0).unwrap();
                }
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("rust_bitcoin", |b| {
        b.iter_batched_ref(
            || {
                test_blocks
                    .iter()
                    .map(|block| bitcoin::Block::consensus_decode(&mut &block[..]).unwrap())
                    .collect::<Vec<_>>()
            },
            |rust_btc_parsed| {
                for block in rust_btc_parsed {
                    // let mut buf = Vec::new();
                    let mut buf = Vec::with_capacity(max_block_size);
                    // buf.clear();
                    block.consensus_encode(&mut buf).unwrap();
                }
            },
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

/// Benchmark serializing 1K bitcoin blocks, but collect data on each block
fn bench_serialize_bitcoin_1k_blocks(c: &mut Criterion) {
    let test_blocks = load_bitcoin_blocks("benches/data/sampled_blocks.txt");

    // Get the largest block size
    let max_block_size = test_blocks.iter().map(|block| block.len()).max().unwrap();

    let mut group = c.benchmark_group("serialize_bitcoin_1k_blocks");
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(100));
    group.measurement_time(Duration::from_millis(200));

    for (i, test_block) in test_blocks.iter().enumerate() {
        group.bench_function(format!("vest_{}", i), |b| {
            b.iter_batched_ref(
                || parse_block(test_block).unwrap().1,
                |vest_block| {
                    let mut buf = vec![0; max_block_size];
                    serialize_block(vest_block, &mut buf, 0).unwrap();
                },
                BatchSize::SmallInput,
            )
        });

        group.bench_function(format!("rust_bitcoin_{}", i), |b| {
            b.iter_batched(
                || bitcoin::Block::consensus_decode(&mut &test_block[..]).unwrap(),
                |rust_block| {
                    // let mut buf = Vec::with_capacity(max_block_size);
                    let mut buf = Vec::new();
                    rust_block.consensus_encode(&mut buf).unwrap();
                },
                BatchSize::SmallInput,
            )
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_parse_bitcoin_1k_blocks_bulk,
    // bench_parse_bitcoin_1k_blocks,
    bench_serialize_bitcoin_1k_blocks_bulk,
    // bench_serialize_bitcoin_1k_blocks,
);
criterion_main!(benches);
