#![allow(unused)]

extern crate rustls;
extern crate tls;

use criterion::Throughput;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use tls::tls13_testvector::*;
use tls::tls_combinators;
use tls::tls_combinators::ClientHelloExtensionExtensionData::*;
// use tls::tls_combinators::KeyShareEntryKeyExchange::*;
use tls::tls_combinators::ServerNameName::HostName;
use tls::tls_combinators::*;
use vest::properties::*;
use vest::regular::repeat::RepeatResult;

use rustls::internal::msgs::codec::*;

#[rustfmt::skip]
static CLIENT_HELLO_RECORD: &[u8] = &[
    // record header
    0x16, 0x03, 0x01, 0x00, 0xf8,
    // handshake header
    0x01, 0x00, 0x00, 0xf4,
    // client version
    0x03, 0x03, 
    // random
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
    // legacy session id
    0x20, 0xe0, 0xe1, 0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xeb, 0xec, 0xed, 0xee,
    0xef, 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff, 
    // cipher suites
    0x00, 0x08, 0x13, 0x02, 0x13, 0x03, 0x13, 0x01, 0x00, 0xff, 
    // legacy compression methods
    0x01, 0x00, 
    // extension length
    0x00, 0xa3,
    // extension - server name
    0x00, 0x00, 0x00, 0x18, 0x00, 0x16, 0x00, 0x00, 0x13, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65,
    0x2e, 0x75, 0x6c, 0x66, 0x68, 0x65, 0x69, 0x6d, 0x2e, 0x6e, 0x65, 0x74, 
    // extension - EC point formats
    0x00, 0x0b, 0x00, 0x04, 0x03, 0x00, 0x01, 0x02,
    // extension - supported groups
    0x00, 0x0a, 0x00, 0x16, 0x00, 0x14, 0x00, 0x1d, 0x00, 0x17, 0x00, 0x1e, 0x00, 0x19, 0x00, 0x18,
    0x01, 0x00, 0x01, 0x01, 0x01, 0x02, 0x01, 0x03, 0x01, 0x04,
    // extension - session ticket
    0x00, 0x23, 0x00, 0x00,
    // extension - Encrypt-then-MAC
    0x00, 0x16, 0x00, 0x00,
    // extension - extended master secret
    0x00, 0x17, 0x00, 0x00,
    // extension - signature algorithms
    0x00, 0x0d, 0x00, 0x1e, 0x00, 0x1c, 0x04, 0x03, 0x05, 0x03, 0x06, 0x03, 0x08, 0x07, 0x08, 0x08,
    0x08, 0x09, 0x08, 0x0a, 0x08, 0x0b, 0x08, 0x04, 0x08, 0x05, 0x08, 0x06, 0x04, 0x01, 0x05, 0x01, 0x06, 0x01,
    // extension - supported versions
    0x00, 0x2b, 0x00, 0x03, 0x02, 0x03, 0x04,
    // extension - psk key exchange modes
    0x00, 0x2d, 0x00, 0x02, 0x01, 0x01,
    // extension - key share
    0x00, 0x33, 0x00, 0x26, 0x00, 0x24, 0x00, 0x1d, 0x00, 0x20, 0x35, 0x80, 0x72, 0xd6, 0x36, 0x58,
    0x80, 0xd1, 0xae, 0xea, 0x32, 0x9a, 0xdf, 0x91, 0x21, 0x38, 0x38, 0x51, 0xed, 0x21, 0xa2, 0x8e,
    0x3b, 0x75, 0xe9, 0x65, 0xd0, 0xd2, 0xcd, 0x16, 0x62, 0x54,
];

fn handshake_msg_payloads() -> [(&'static str, &'static [u8]); 7] {
    [
        ("Handshake-ClientHello", &CLIENT_HELLO_RECORD[5..]),
        ("Handshake-ServerHello", &SERVER_HELLO_RECORD[5..]),
        (
            "Handshake-EncryptedExtensions",
            ENCRTPTED_EXTENSIONS_HANDSHAKE,
        ),
        ("Handshake-Certificate", CERTIFICATE_HANDSHAKE),
        ("Handshake-CertificateVerify", CERTIFICATEVERIFY_HANDSHAKE),
        ("Handshake-ServerFinished", SERVER_FINISHED_HANDSHAKE),
        ("Handshake-ClientFinished", CLIENT_FINISHED_HANDSHAKE),
    ]
}

fn vesttls_handshake_msgs<'a>() -> [Handshake<'a>; 7] {
    handshake_msg_payloads().map(|(_, payload)| handshake().parse(payload).unwrap().1)
}

fn rustls_handshake_msgs<'a>() -> [rustls::internal::msgs::handshake::HandshakeMessagePayload<'a>; 7]
{
    handshake_msg_payloads().map(|(_, payload)| {
        match rustls::internal::msgs::message::MessagePayload::new(
            rustls::ContentType::Handshake,
            rustls::ProtocolVersion::TLSv1_3,
            payload,
        )
        .unwrap()
        {
            rustls::internal::msgs::message::MessagePayload::Handshake { parsed, .. } => parsed,
            _ => unreachable!(),
        }
    })
}

fn vesttls_client_hello_parse(c: &mut Criterion) {
    c.bench_function("vesttls_client_hello_parse", |b| {
        b.iter(|| {
            client_hello()
                .parse(&CLIENT_HELLO_RECORD[9..])
                .unwrap_or_else(|e| {
                    panic!("Failed to parse ClientHello: {}", e);
                })
        })
    });
}

fn rustls_client_hello_parse(c: &mut Criterion) {
    c.bench_function("rustls_client_hello_parse", |b| {
        b.iter(|| {
            let mut rd = rustls::internal::msgs::codec::Reader::init(&CLIENT_HELLO_RECORD[9..]);
            rustls::internal::msgs::handshake::ClientHelloPayload::read(&mut rd).unwrap_or_else(
                |e| {
                    panic!("Failed to parse ClientHello: {:?}", e);
                },
            )
        })
    });
}

fn vesttls_parse_handshake(c: &mut Criterion) {
    c.bench_function("vesttls_handshake_parse_iter_time", |b| {
        b.iter(|| {
            for (_, payload) in handshake_msg_payloads() {
                black_box(handshake().parse(payload).unwrap_or_else(|e| {
                    panic!("Failed to parse Handshake: {}", e);
                }));
            }
        })
    });
}

fn rustls_parse_handshake(c: &mut Criterion) {
    c.bench_function("rustls_handshake_parse_iter_time", |b| {
        b.iter(|| {
            for (_, payload) in handshake_msg_payloads() {
                black_box(
                    rustls::internal::msgs::message::MessagePayload::new(
                        rustls::ContentType::Handshake,
                        rustls::ProtocolVersion::TLSv1_3,
                        payload,
                    )
                    .unwrap_or_else(|e| {
                        panic!("Failed to parse Handshake: {:?}", e);
                    }),
                );
            }
        })
    });
}

fn vesttls_parse_handshake_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("vesttls_handshake_parse_throughput");
    for &(name, payload) in handshake_msg_payloads().iter() {
        group.throughput(Throughput::Bytes(payload.len() as u64));
        group.bench_with_input(format!("Parse {}", name), payload, |b, payload| {
            b.iter(|| {
                black_box(handshake().parse(payload).unwrap_or_else(|e| {
                    panic!("Failed to parse Handshake: {}", e);
                }));
            })
        });
    }
    group.finish();
}

fn rustls_parse_handshake_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("rustls_handshake_parse_throughput");
    for &(name, payload) in handshake_msg_payloads().iter() {
        group.throughput(Throughput::Bytes(payload.len() as u64));
        group.bench_with_input(format!("Parse {}", name), payload, |b, payload| {
            b.iter(|| {
                black_box(
                    rustls::internal::msgs::message::MessagePayload::new(
                        rustls::ContentType::Handshake,
                        rustls::ProtocolVersion::TLSv1_3,
                        payload,
                    )
                    .unwrap_or_else(|e| {
                        panic!("Failed to parse Handshake: {:?}", e);
                    }),
                );
            })
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    vesttls_parse_handshake_throughput,
    rustls_parse_handshake_throughput
);
// criterion_group!(
//     benches,
//     vesttls_parse_handshake,
//     rustls_parse_handshake,
//     // vesttls_client_hello_parse,
//     // rustls_client_hello_parse,
// );
criterion_main!(benches);
