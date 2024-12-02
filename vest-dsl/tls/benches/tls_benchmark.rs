#![allow(unused)]

extern crate rustls;
extern crate tls;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use tls::tls13_testvector::*;
use tls::tls_combinators;
use tls::tls_combinators::ClientHelloExtensionExtensionData::*;
use tls::tls_combinators::KeyShareEntryKeyExchange::*;
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

fn vesttls_client_hello_serialize(c: &mut Criterion) {
    fn client_hello_serialize() -> Result<usize, vest::errors::SerializeError> {
        let client_hello_record: ClientHello<'_> = ClientHello {
            legacy_version: 771,
            random: &[
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 25, 26, 27, 28, 29, 30, 31,
            ],
            legacy_session_id: SessionId {
                l: 32,
                id: &[
                    224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239,
                    240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255,
                ],
            },
            cipher_suites: CipherSuiteList {
                l: 8,
                list: RepeatResult(vec![4866, 4867, 4865, 255]),
            },
            legacy_compression_methods: Opaque1Ff { l: 1, data: &[0] },
            extensions: ClientExtensions {
                l: 163,
                // extensions: &[
                //     0, 0, 0, 24, 0, 22, 0, 0, 19, 101, 120, 97, 109, 112, 108, 101, 46, 117, 108,
                //     102, 104, 101, 105, 109, 46, 110, 101, 116, 0, 11, 0, 4, 3, 0, 1, 2, 0, 10, 0,
                //     22, 0, 20, 0, 29, 0, 23, 0, 30, 0, 25, 0, 24, 1, 0, 1, 1, 1, 2, 1, 3, 1, 4, 0,
                //     35, 0, 0, 0, 22, 0, 0, 0, 23, 0, 0, 0, 13, 0, 30, 0, 28, 4, 3, 5, 3, 6, 3, 8,
                //     7, 8, 8, 8, 9, 8, 10, 8, 11, 8, 4, 8, 5, 8, 6, 4, 1, 5, 1, 6, 1, 0, 43, 0, 3,
                //     2, 3, 4, 0, 45, 0, 2, 1, 1, 0, 51, 0, 38, 0, 36, 0, 29, 0, 32, 53, 128, 114,
                //     214, 54, 88, 128, 209, 174, 234, 50, 154, 223, 145, 33, 56, 56, 81, 237, 33,
                //     162, 142, 59, 117, 233, 101, 208, 210, 205, 22, 98, 84,
                // ],
                extensions: RepeatResult(vec![
                    ClientHelloExtension {
                        extension_type: 0,
                        ext_len: 24,
                        extension_data: ServerName(ServerNameList {
                            l: 22,
                            list: RepeatResult(vec![tls_combinators::ServerName {
                                name_type: 0,
                                name: HostName(Opaque1Ffff {
                                    l: 19,
                                    data: &[
                                        101, 120, 97, 109, 112, 108, 101, 46, 117, 108, 102, 104,
                                        101, 105, 109, 46, 110, 101, 116,
                                    ],
                                }),
                            }]),
                        }),
                    },
                    ClientHelloExtension {
                        extension_type: 11,
                        ext_len: 4,
                        extension_data: ECPointFormats(EcPointFormatList {
                            l: 3,
                            list: RepeatResult(vec![0, 1, 2]),
                        }),
                    },
                    ClientHelloExtension {
                        extension_type: 10,
                        ext_len: 22,
                        extension_data: SupportedGroups(NamedGroupList {
                            l: 20,
                            list: RepeatResult(vec![29, 23, 30, 25, 24, 256, 257, 258, 259, 260]),
                        }),
                    },
                    ClientHelloExtension {
                        extension_type: 35,
                        ext_len: 0,
                        extension_data: SessionTicket(&[]),
                    },
                    ClientHelloExtension {
                        extension_type: 22,
                        ext_len: 0,
                        extension_data: EncryptThenMac(&[]),
                    },
                    ClientHelloExtension {
                        extension_type: 23,
                        ext_len: 0,
                        extension_data: ExtendedMasterSecret(&[]),
                    },
                    ClientHelloExtension {
                        extension_type: 13,
                        ext_len: 30,
                        extension_data: SignatureAlgorithms(SignatureSchemeList {
                            l: 28,
                            list: RepeatResult(vec![
                                1027, 1283, 1539, 2055, 2056, 2057, 2058, 2059, 2052, 2053, 2054,
                                1025, 1281, 1537,
                            ]),
                        }),
                    },
                    ClientHelloExtension {
                        extension_type: 43,
                        ext_len: 3,
                        extension_data: SupportedVersions(SupportedVersionsClient {
                            l: 2,
                            versions: RepeatResult(vec![772]),
                        }),
                    },
                    ClientHelloExtension {
                        extension_type: 45,
                        ext_len: 2,
                        extension_data: PskKeyExchangeModes(tls_combinators::PskKeyExchangeModes {
                            l: 1,
                            modes: RepeatResult(vec![1]),
                        }),
                    },
                    ClientHelloExtension {
                        extension_type: 51,
                        ext_len: 38,
                        extension_data: KeyShare(KeyShareClientHello {
                            l: 36,
                            client_shares: RepeatResult(vec![KeyShareEntry {
                                group: 29,
                                l: 32,
                                key_exchange: X25519(&[
                                    53, 128, 114, 214, 54, 88, 128, 209, 174, 234, 50, 154, 223,
                                    145, 33, 56, 56, 81, 237, 33, 162, 142, 59, 117, 233, 101, 208,
                                    210, 205, 22, 98, 84,
                                ]),
                            }]),
                        }),
                    },
                ]),
            },
        };
        let mut outbuf = vec![0u8; 250];
        client_hello().serialize(client_hello_record, &mut outbuf, 0)
    }
    c.bench_function("vesttls_client_hello_serialize", |b| {
        b.iter(|| client_hello_serialize())
    });
}

fn vesttls_parse_handshake(c: &mut Criterion) {
    c.bench_function("vesttls_handshake_parse", |b| {
        b.iter(|| {
            for payload in [
                &CLIENT_HELLO_RECORD[5..],
                &SERVER_HELLO_RECORD[5..],
                ENCRTPTED_EXTENSIONS_HANDSHAKE,
                CERTIFICATE_HANDSHAKE,
                CERTIFICATEVERIFY_HANDSHAKE,
                SERVER_FINISHED_HANDSHAKE,
                CLIENT_FINISHED_HANDSHAKE,
            ] {
                black_box(handshake().parse(payload).unwrap_or_else(|e| {
                    panic!("Failed to parse Handshake: {}", e);
                }));
            }
        })
    });
}

fn rustls_parse_handshake(c: &mut Criterion) {
    c.bench_function("vesttls_handshake_parse", |b| {
        b.iter(|| {
            for payload in [
                &CLIENT_HELLO_RECORD[5..],
                &SERVER_HELLO_RECORD[5..],
                ENCRTPTED_EXTENSIONS_HANDSHAKE,
                CERTIFICATE_HANDSHAKE,
                CERTIFICATEVERIFY_HANDSHAKE,
                SERVER_FINISHED_HANDSHAKE,
                CLIENT_FINISHED_HANDSHAKE,
            ] {
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

criterion_group!(
    benches,
    vesttls_parse_handshake,
    rustls_parse_handshake,
    // vesttls_client_hello_parse,
    // rustls_client_hello_parse,
    // vesttls_client_hello_serialize
);
criterion_main!(benches);
