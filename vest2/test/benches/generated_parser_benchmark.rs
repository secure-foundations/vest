#![allow(unused)]

extern crate test as vest2_generated;

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use std::time::Duration;

use criterion::Throughput;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

use rustls::internal::msgs::message::MessagePayload;
use vest_lib2::core::exec::parser::Parser;
use vest_lib2::core::exec::serializer::Serializer;

use vest2_generated::bitcoin::BlockFmt;
use vest2_generated::tls::HandshakeFmt;

use base64::prelude::*;
use bitcoin::consensus::{Decodable, Encodable};
use rustls::internal::msgs::base::Payload;
use rustls::internal::msgs::codec::Codec;

/// Load blocks stored in bench_data/bitcoin/sampled_blocks.txt
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

/// Load TLS handshakes from local module
fn load_tls_handshakes() -> Vec<Vec<u8>> {
    mod handshakes {
        include!("../bench_data/tls/tranco_handshakes.rs");
    }

    let mut messages = Vec::new();
    for (_domain, client_msgs, server_msgs) in handshakes::HANDSHAKE_DATA {
        for msg in *client_msgs {
            messages.push(msg.to_vec());
        }
        for msg in *server_msgs {
            messages.push(msg.to_vec());
        }
    }
    messages
}

/// Benchmark Bitcoin parsing
fn bench_parse_bitcoin_bulk(c: &mut Criterion) {
    let test_blocks = load_bitcoin_blocks("bench_data/bitcoin/sampled_blocks.txt");

    println!("Loaded {} Bitcoin blocks", test_blocks.len());

    // Verify both parsers can parse all blocks
    {
        let block_fmt = BlockFmt;
        for (i, block_bytes) in test_blocks.iter().enumerate() {
            match block_fmt.parse(&&block_bytes[..]) {
                Ok(_) => {}
                Err(e) => panic!("Generated parser failed on block {}: {:?}", i, e),
            }
        }

        for (i, block_bytes) in test_blocks.iter().enumerate() {
            match bitcoin::Block::consensus_decode(&mut &block_bytes[..]) {
                Ok(_) => {}
                Err(e) => panic!("Bitcoin library parser failed on block {}: {:?}", i, e),
            }
        }
    }

    let total_bytes: u64 = test_blocks.iter().map(|b| b.len() as u64).sum();

    let mut group = c.benchmark_group("bitcoin_parse");
    group.throughput(Throughput::Bytes(total_bytes));

    group.bench_function("generated_parser", |b| {
        let block_fmt = BlockFmt;
        b.iter(|| {
            for block_bytes in test_blocks.iter() {
                let _ = block_fmt.parse(&black_box(&block_bytes[..]));
            }
        })
    });

    group.bench_function("bitcoin_library", |b| {
        b.iter(|| {
            for block_bytes in test_blocks.iter() {
                let _ = bitcoin::Block::consensus_decode(&mut &block_bytes[..]);
            }
        })
    });

    group.finish();
}

/// Benchmark TLS handshake parsing
fn bench_parse_tls_bulk(c: &mut Criterion) {
    let tls_messages = load_tls_handshakes();

    println!("Loaded {} TLS handshake messages", tls_messages.len());

    // Verify both parsers can parse all messages and count retained corpus
    let mut retained_messages = Vec::new();
    let mut retained_bytes = 0u64;
    {
        let handshake_fmt = HandshakeFmt;
        for msg in &tls_messages {
            // Try generated parser
            let generated_ok = handshake_fmt.parse(&&msg[..]).is_ok();

            let rustls_ok = parse_rustls_handshake(msg.clone()).is_ok();
            if generated_ok && rustls_ok {
                retained_bytes += msg.len() as u64;
                retained_messages.push(msg.clone());
            }
        }
    }

    println!(
        "Retained {} / {} messages ({} bytes)",
        retained_messages.len(),
        tls_messages.len(),
        retained_bytes
    );

    let mut group = c.benchmark_group("tls_parse");
    group.throughput(Throughput::Bytes(retained_bytes));

    group.bench_function("generated_parser", |b| {
        let handshake_fmt = HandshakeFmt;
        b.iter(|| {
            for msg in retained_messages.iter() {
                let _ = handshake_fmt.parse(&black_box(&msg[..]));
            }
        })
    });

    group.bench_function("rustls_library", |b| {
        b.iter(|| {
            let messages = retained_messages.clone();
            for msg in messages.into_iter() {
                let _ = parse_rustls_handshake(black_box(msg));
            }
        })
    });

    group.finish();
}

/// Parse a TLS handshake message using rustls 0.23.40 public API
fn parse_rustls_handshake(data: Vec<u8>) -> Result<MessagePayload, Box<dyn std::error::Error>> {
    let payload = Payload::new(data);
    match MessagePayload::new(
        rustls::ContentType::Handshake,
        rustls::ProtocolVersion::TLSv1_3,
        payload,
    ) {
        Ok(m) => Ok(m),
        Err(e) => Err(format!("{:?}", e).into()),
    }
}

/// Benchmark Bitcoin serialization
fn bench_serialize_bitcoin_bulk(c: &mut Criterion) {
    let test_blocks = load_bitcoin_blocks("bench_data/bitcoin/sampled_blocks.txt");

    let block_fmt = BlockFmt;
    let vest_blocks: Vec<_> = test_blocks
        .iter()
        .map(|b| block_fmt.parse(&&b[..]).unwrap().1)
        .collect();

    let rust_blocks: Vec<_> = test_blocks
        .iter()
        .map(|b| bitcoin::Block::consensus_decode(&mut &b[..]).unwrap())
        .collect();

    let total_bytes: u64 = test_blocks.iter().map(|b| b.len() as u64).sum();
    let max_block_size = test_blocks.iter().map(|block| block.len()).max().unwrap();

    let mut group = c.benchmark_group("bitcoin_serialize");
    group.throughput(Throughput::Bytes(total_bytes));

    group.bench_function("generated_serializer", |b| {
        b.iter(|| {
            for block in &vest_blocks {
                let mut buf = Vec::with_capacity(max_block_size);
                block_fmt.serialize(block, &mut buf);
                black_box(buf);
            }
        })
    });

    group.bench_function("bitcoin_library", |b| {
        b.iter(|| {
            for block in &rust_blocks {
                let mut buf = Vec::with_capacity(max_block_size);
                block.consensus_encode(&mut buf).unwrap();
                black_box(buf);
            }
        })
    });

    group.finish();
}

/// Benchmark TLS handshake serialization
fn bench_serialize_tls_bulk(c: &mut Criterion) {
    let tls_messages = load_tls_handshakes();

    // Verify both parsers can parse all messages and collect only matching ones
    let mut retained_vest_msgs = Vec::new();
    let mut retained_rustls_msgs = Vec::new();
    let mut retained_bytes = 0u64;
    let mut max_msg_size = 0;

    let handshake_fmt = HandshakeFmt;
    for msg in &tls_messages {
        let generated_parsed = handshake_fmt.parse(&&msg[..]);
        let rustls_parsed = parse_rustls_handshake(msg.clone());

        if let (Ok((_, g_val)), Ok(MessagePayload::Handshake { parsed: r_val, .. })) =
            (generated_parsed, rustls_parsed)
        {
            retained_bytes += msg.len() as u64;
            if msg.len() > max_msg_size {
                max_msg_size = msg.len();
            }
            retained_vest_msgs.push(g_val);
            retained_rustls_msgs.push(r_val);
        }
    }

    println!(
        "Retained {} / {} messages for serialization bench ({} bytes)",
        retained_vest_msgs.len(),
        tls_messages.len(),
        retained_bytes
    );

    let mut group = c.benchmark_group("tls_serialize");
    group.throughput(Throughput::Bytes(retained_bytes));

    group.bench_function("generated_serializer", |b| {
        b.iter(|| {
            for msg in &retained_vest_msgs {
                let mut buf = Vec::with_capacity(max_msg_size);
                handshake_fmt.serialize(msg, &mut buf);
                black_box(buf);
            }
        })
    });

    group.bench_function("rustls_library", |b| {
        b.iter(|| {
            for msg in &retained_rustls_msgs {
                let mut buf = Vec::with_capacity(max_msg_size);
                msg.encode(&mut buf);
                black_box(buf);
            }
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_parse_bitcoin_bulk,
    bench_parse_tls_bulk,
    bench_serialize_bitcoin_bulk,
    bench_serialize_tls_bulk
);
criterion_main!(benches);
