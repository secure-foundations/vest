use base64::prelude::*;
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use vest_bitcoin::vest_bitcoin::{block_len, parse_block, serialize_block};
use vps_lib::core::exec::parser::Parser;
use vps_lib::core::exec::serializer::{Prepare, SerializerExt};
use vest_tls::tls_combinators::{handshake_len, parse_handshake, serialize_handshake};
use vps_generated::bitcoin::BlockFmt;
use vps_generated::tls::HandshakeFmt;

fn load_bitcoin_blocks() -> Vec<Vec<u8>> {
    let path = std::env::var_os("VPS_BITCOIN_CORPUS")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../../../vest-dsl-vps/test/bench_data/bitcoin/sampled_blocks.txt")
        });
    BufReader::new(File::open(path).expect("open Bitcoin corpus"))
        .lines()
        .map(|line| BASE64_STANDARD.decode(line.unwrap()).unwrap())
        .collect()
}

fn load_tls_handshakes() -> Vec<Vec<u8>> {
    mod handshakes {
        include!("../../../../vest-dsl-vps/test/bench_data/tls/tranco_handshakes.rs");
    }
    handshakes::HANDSHAKE_DATA
        .iter()
        .flat_map(|(_, client, server)| client.iter().chain(server.iter()))
        .map(|message| message.to_vec())
        .collect()
}

fn bitcoin_parse(c: &mut Criterion) {
    let inputs = load_bitcoin_blocks();
    let bytes = inputs.iter().map(|x| x.len() as u64).sum();
    assert!(inputs.iter().all(|x| parse_block(x).is_ok()));
    assert!(inputs.iter().all(|x| BlockFmt.parse(&&x[..]).is_ok()));
    let mut group = c.benchmark_group("vest_vps/bitcoin/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(parse_block(black_box(input)).unwrap());
            }
        })
    });
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(BlockFmt.parse(black_box(&&input[..])).unwrap());
            }
        })
    });
    group.finish();
}

fn bitcoin_serialize(c: &mut Criterion) {
    let inputs = load_bitcoin_blocks();
    let bytes = inputs.iter().map(|x| x.len() as u64).sum();
    let vest_values: Vec<_> = inputs.iter().map(|x| parse_block(x).unwrap().1).collect();
    let vps_values: Vec<_> = inputs
        .iter()
        .map(|x| BlockFmt.parse(&&x[..]).unwrap().1)
        .collect();
    let vest_lengths: Vec<_> = vest_values.iter().map(|x| block_len(x)).collect();
    let vps_lengths: Vec<_> = vps_values.iter().map(|x| BlockFmt.prepare(x).unwrap()).collect();
    let mut vest_outputs: Vec<Vec<u8>> = vest_lengths.iter().map(|n| vec![0; *n]).collect();
    let mut vps_outputs: Vec<Vec<u8>> = vps_lengths.iter().map(|n| vec![0; *n]).collect();
    let mut vps_vec_outputs: Vec<Vec<u8>> =
        vps_lengths.iter().map(|n| Vec::with_capacity(*n)).collect();

    let mut group = c.benchmark_group("vest_vps/bitcoin/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for (value, output) in vest_values.iter().zip(&mut vest_outputs) {
                black_box(serialize_block(value, black_box(output), 0).unwrap());
            }
        })
    });
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for (value, output) in vps_values.iter().zip(&mut vps_outputs) {
                BlockFmt.serialize(value, black_box(output.as_mut_slice()));
                black_box(&output);
            }
        })
    });
    group.bench_function("VPS-Vec", |b| {
        b.iter(|| {
            for (value, output) in vps_values.iter().zip(&mut vps_vec_outputs) {
                output.clear();
                BlockFmt.serialize_with_vec(value, black_box(output));
                black_box(&output);
            }
        })
    });
    group.finish();
}

fn tls_parse(c: &mut Criterion) {
    let all_inputs = load_tls_handshakes();
    let inputs: Vec<_> = all_inputs
        .into_iter()
        .filter(|x| parse_handshake(x).is_ok() && HandshakeFmt.parse(&&x[..]).is_ok())
        .collect();
    let bytes = inputs.iter().map(|x| x.len() as u64).sum();
    eprintln!("TLS common corpus: {} messages, {} bytes", inputs.len(), bytes);
    let mut group = c.benchmark_group("vest_vps/tls/parse");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(parse_handshake(black_box(input)).unwrap());
            }
        })
    });
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for input in &inputs {
                black_box(HandshakeFmt.parse(black_box(&&input[..])).unwrap());
            }
        })
    });
    group.finish();
}

fn tls_serialize(c: &mut Criterion) {
    let inputs: Vec<_> = load_tls_handshakes()
        .into_iter()
        .filter(|x| parse_handshake(x).is_ok() && HandshakeFmt.parse(&&x[..]).is_ok())
        .collect();
    let bytes = inputs.iter().map(|x| x.len() as u64).sum();
    let vest_values: Vec<_> = inputs.iter().map(|x| parse_handshake(x).unwrap().1).collect();
    let vps_values: Vec<_> = inputs
        .iter()
        .map(|x| HandshakeFmt.parse(&&x[..]).unwrap().1)
        .collect();
    let vest_lengths: Vec<_> = vest_values.iter().map(|x| handshake_len(x)).collect();
    let vps_lengths: Vec<_> = vps_values
        .iter()
        .map(|x| HandshakeFmt.prepare(x).unwrap())
        .collect();
    let mut vest_outputs: Vec<Vec<u8>> = vest_lengths.iter().map(|n| vec![0; *n]).collect();
    let mut vps_outputs: Vec<Vec<u8>> = vps_lengths.iter().map(|n| vec![0; *n]).collect();
    let mut vps_vec_outputs: Vec<Vec<u8>> =
        vps_lengths.iter().map(|n| Vec::with_capacity(*n)).collect();

    let mut group = c.benchmark_group("vest_vps/tls/serialize");
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("Vest", |b| {
        b.iter(|| {
            for (value, output) in vest_values.iter().zip(&mut vest_outputs) {
                black_box(serialize_handshake(value, black_box(output), 0).unwrap());
            }
        })
    });
    group.bench_function("VPS", |b| {
        b.iter(|| {
            for (value, output) in vps_values.iter().zip(&mut vps_outputs) {
                HandshakeFmt.serialize(value, black_box(output.as_mut_slice()));
                black_box(&output);
            }
        })
    });
    group.bench_function("VPS-Vec", |b| {
        b.iter(|| {
            for (value, output) in vps_values.iter().zip(&mut vps_vec_outputs) {
                output.clear();
                HandshakeFmt.serialize_with_vec(value, black_box(output));
                black_box(&output);
            }
        })
    });
    group.finish();
}

criterion_group!(benches, bitcoin_parse, bitcoin_serialize, tls_parse, tls_serialize);
criterion_main!(benches);
