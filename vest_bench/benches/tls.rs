//! Vest's TLS 1.3 handshake codec compared with Rustls 0.22's message codec,
//! over the handshakes captured from public servers and Chrome in
//! `corpora/tls/`.
//!
//! Each handshake message type is its own group because their shapes differ:
//! ClientHellos are extension lists, Certificates are mostly opaque
//! certificate bytes, and Finished messages are a header and a MAC. Unlike the
//! microbenchmarks in `formats.rs`, each implementation uses its native Rust
//! value type.

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion, Throughput};
use rustls::internal::msgs::base::Payload;
use rustls::internal::msgs::codec::Codec;
use vest_bench::real;
use vest_lib::core::exec::parser::Parser;
use vest_lib::core::exec::serializer::{Prepare, SerializerExt};
use vest_tests::tls::HandshakeFmt;

#[path = "support/tls.rs"]
mod checks;
use checks::parse as parse_rustls;

/// Benchmark groups, each with the corpus message kinds it measures. A
/// HelloRetryRequest is a ServerHello on the wire.
const GROUPS: [(&str, &[&str]); 7] = [
    ("client_hello", &["client_hello"]),
    ("server_hello", &["server_hello", "hello_retry_request"]),
    ("encrypted_extensions", &["encrypted_extensions"]),
    ("certificate", &["certificate"]),
    ("certificate_verify", &["certificate_verify"]),
    ("finished", &["finished"]),
    ("new_session_ticket", &["new_session_ticket"]),
];

/// Every message must parse with both codecs and re-encode to its own bytes,
/// so the two serializers are measured producing the same output.
fn validate(name: &str, inputs: &[Vec<u8>]) {
    assert!(!inputs.is_empty(), "no {name} messages in the corpus");
    let mut encoded = Vec::new();
    for input in inputs {
        assert!(input.len() >= 4);
        let body_len = u32::from_be_bytes([0, input[1], input[2], input[3]]) as usize;
        assert_eq!(
            body_len + 4,
            input.len(),
            "trailing or incomplete TLS handshake"
        );
        let (n, value) = HandshakeFmt.parse(&&input[..]).unwrap();
        assert_eq!(n, input.len());
        encoded.resize(HandshakeFmt.prepare(&value).unwrap(), 0);
        HandshakeFmt.serialize(&value, encoded.as_mut_slice());
        assert_eq!(&encoded, input, "Vest re-encodes a {name} differently");

        encoded.clear();
        parse_rustls(&mut Payload::new(input.clone())).encode(&mut encoded);
        assert_eq!(&encoded, input, "Rustls re-encodes a {name} differently");
    }
}

fn parse(c: &mut Criterion) {
    let corpus = real::tls_handshakes();
    for (name, kinds) in GROUPS {
        let inputs: Vec<Vec<u8>> = corpus
            .iter()
            .filter(|m| kinds.contains(&m.message.as_str()))
            .map(|m| m.bytes.clone())
            .collect();
        validate(name, &inputs);
        let bytes = inputs.iter().map(|input| input.len() as u64).sum();
        let mut group = c.benchmark_group(format!("tls/{name}/parse"));
        group.throughput(Throughput::Bytes(bytes));
        group.bench_function("Vest", |b| {
            b.iter(|| {
                for input in &inputs {
                    black_box(HandshakeFmt.parse(black_box(&&input[..])).unwrap());
                }
            })
        });
        group.bench_function("Rustls", |b| {
            b.iter_batched_ref(
                || inputs.iter().cloned().map(Payload::new).collect::<Vec<_>>(),
                |payloads| {
                    for payload in payloads {
                        black_box(parse_rustls(black_box(payload)));
                    }
                },
                BatchSize::LargeInput,
            )
        });
        group.finish();
    }
}

fn serialize(c: &mut Criterion) {
    let corpus = real::tls_handshakes();
    for (name, kinds) in GROUPS {
        let inputs: Vec<&[u8]> = corpus
            .iter()
            .filter(|m| kinds.contains(&m.message.as_str()))
            .map(|m| &m.bytes[..])
            .collect();
        let vest_values: Vec<_> = inputs
            .iter()
            .map(|input| HandshakeFmt.parse(input).unwrap().1)
            .collect();
        let baseline_values: Vec<_> = inputs
            .iter()
            .map(|input| parse_rustls(&mut Payload::new(input.to_vec())))
            .collect();
        let lengths: Vec<_> = vest_values
            .iter()
            .map(|value| HandshakeFmt.prepare(value).unwrap())
            .collect();
        let bytes = lengths.iter().map(|length| *length as u64).sum();
        validate(
            name,
            &inputs
                .iter()
                .map(|input| input.to_vec())
                .collect::<Vec<_>>(),
        );
        let capacity = lengths.iter().copied().max().unwrap();
        let mut vest_output = vec![0; capacity];
        let mut baseline_output = Vec::with_capacity(capacity);

        let mut group = c.benchmark_group(format!("tls/{name}/serialize"));
        group.throughput(Throughput::Bytes(bytes));
        group.bench_function("Vest", |b| {
            b.iter(|| {
                for (value, length) in vest_values.iter().zip(&lengths) {
                    let output = &mut vest_output[..*length];
                    HandshakeFmt.serialize(black_box(value), black_box(output));
                    black_box(&vest_output[..*length]);
                }
            })
        });
        group.bench_function("Rustls", |b| {
            b.iter(|| {
                for value in &baseline_values {
                    baseline_output.clear();
                    black_box(value).encode(black_box(&mut baseline_output));
                    black_box(&baseline_output);
                }
            })
        });
        group.finish();
    }
}

criterion_group!(benches, parse, serialize);
criterion_main!(benches);
