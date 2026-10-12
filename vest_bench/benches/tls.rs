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

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use rustls::internal::msgs::base::Payload;
use rustls::internal::msgs::codec::Codec;
use vest_bench::corpora;
use vest_lib::core::exec::parser::Parser;
use vest_lib::core::exec::serializer::{Prepare, SerializerExt};
use vest_tests::tls::HandshakeFmt;

#[path = "shared/tls.rs"]
mod checks;
#[path = "shared/timing.rs"]
mod harness;
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
    let corpus = corpora::tls_handshakes();
    for (name, kinds) in GROUPS {
        let inputs: Vec<Vec<u8>> = corpus
            .iter()
            .filter(|m| kinds.contains(&m.message.as_str()))
            .map(|m| m.bytes.clone())
            .collect();
        validate(name, &inputs);
        let mut payloads: Vec<_> = inputs.iter().cloned().map(Payload::new).collect();
        let bytes = inputs.iter().map(|input| input.len() as u64).sum();
        harness::corpus_metadata(&format!("tls/{name}/parse"), inputs.len(), bytes);
        let mut group = c.benchmark_group(format!("tls/{name}/parse"));
        group.throughput(Throughput::Bytes(bytes));
        group.bench_function("Vest", |b| {
            harness::retained(b, inputs.len(), |i| {
                HandshakeFmt.parse(black_box(&&inputs[i][..])).unwrap()
            })
        });
        group.bench_function("Rustls", |b| {
            harness::retained(b, payloads.len(), |i| {
                parse_rustls(black_box(&mut payloads[i]))
            })
        });
        group.finish();
    }
}

fn serialize(c: &mut Criterion) {
    let corpus = corpora::tls_handshakes();
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
        harness::corpus_metadata(&format!("tls/{name}/serialize"), inputs.len(), bytes);
        validate(
            name,
            &inputs
                .iter()
                .map(|input| input.to_vec())
                .collect::<Vec<_>>(),
        );
        let capacity = lengths.iter().copied().max().unwrap();
        let mut vest_output = vec![0; capacity];

        let mut group = c.benchmark_group(format!("tls/{name}/serialize"));
        group.throughput(Throughput::Bytes(bytes));
        group.bench_function("Vest", |b| {
            harness::reused(b, || {
                for value in &vest_values {
                    let n = HandshakeFmt.prepare(black_box(value)).unwrap();
                    HandshakeFmt.serialize(black_box(value), black_box(&mut vest_output[..n]));
                    black_box(&vest_output[..n]);
                }
            })
        });
        group.bench_function("Rustls", |b| {
            harness::retained(b, baseline_values.len(), |i| {
                let mut output = Vec::new();
                black_box(&baseline_values[i]).encode(black_box(&mut output));
                output
            })
        });
        group.finish();
    }
}

criterion_group! { name = benches; config = harness::configuration(); targets = parse, serialize }
criterion_main!(benches);
