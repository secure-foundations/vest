//! TLS 1.3 handshake codecs over all captured messages in manifest order.
//! Throughput uses total corpus bytes and pass time, not per-message averages.

use criterion::{criterion_group, criterion_main, Criterion};
use rustls::internal::msgs::{base::Payload, codec::Codec};
use std::hint::black_box;
use vest_bench::{harness::Group, real::tls};
use vest_lib::core::exec::Parser;
use vest_tests::tls::HandshakeFmt;

fn bench(c: &mut Criterion) {
    let inputs: Vec<_> = tls::tls_handshakes().into_iter().map(|m| m.bytes).collect();
    let values = tls::values(&inputs);
    let mut payloads: Vec<_> = inputs.iter().cloned().map(Payload::new).collect();
    let bytes = inputs.iter().map(|input| input.len() as u64).sum();
    let mut group = Group::new(c, "tls/handshakes/parse", inputs.len(), bytes);
    group.retained("Vest", |i| {
        HandshakeFmt
            .parse(black_box(&inputs[i].as_slice()))
            .unwrap()
    });
    group.retained("Rustls", |i| tls::parse(black_box(&mut payloads[i])));
    group.finish();

    let mut group = Group::serializing(c, "tls/handshakes/serialize", &HandshakeFmt, &values.vest);
    group.retained("Rustls", |i| {
        let mut output = Vec::new();
        black_box(&values.rustls[i]).encode(black_box(&mut output));
        output
    });
    group.finish();
}

criterion_group! { name = benches; config = vest_bench::harness::criterion(); targets = bench }
criterion_main!(benches);
