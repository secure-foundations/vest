#![allow(unused)]
pub mod tls13_testvector;
pub mod tls_combinators;

use tls13_testvector::*;
use tls_combinators::ClientHelloExtensionExtensionData::*;
// use tls_combinators::KeyShareEntryKeyExchange::*;
use tls_combinators::ServerNameName::HostName;
use tls_combinators::*;
use vest::properties::*;
use vest::regular::repeat::RepeatResult;

extern crate rustls;
use rustls::internal::msgs::codec::*;

#[rustfmt::skip]
static BYTES_CLIENT_HELLO_RECORD: &[u8] = &[
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

#[rustfmt::skip]
static BYTES_SERVER_HELLO_RECORD: &[u8] = &[
    0x16, 0x03, 0x03, 0x00, 0x7a,
    0x02, 0x00, 0x00, 0x76, 
    0x03, 0x03,
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f,
    0x20, 0xe0, 0xe1, 0xe2 , 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xeb, 0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 
0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff,
    0x13, 0x02, 
    0x00,
    0x00, 0x2e,
    0x00, 0x2b, 0x00, 0x02, 0x03, 0x04,
    0x00, 0x33, 0x00, 0x24, 0x00, 0x1d, 0x00, 0x20, 0x9f, 0xd7, 0xad, 0x6d, 0xcf, 0xf4, 0x29, 0x8d, 0xd3, 0xf9, 0x6d, 0x5b, 0x1b, 0x2a, 0xf9, 0x10, 0xa0, 0x53, 0x5b, 0x14, 0x88, 0xd7 , 0xf8, 0xfa, 0xbb, 0x34, 0x9a, 0x98, 0x28, 0x80, 0xb6, 0x15
];

fn parse_vesttls_client_hello() -> Result<(), Box<dyn std::error::Error>> {
    let (consumed, parsed_client_hello) = client_hello()
        .parse(&BYTES_CLIENT_HELLO_RECORD[9..])
        .unwrap_or_else(|e| {
            panic!("Failed to parse ClientHello: {}", e);
        });
    // println!("consumed: {}", consumed);
    // println!("parsed_client_hello: {:#?}", parsed_client_hello);

    Ok(())
}

fn parse_rustls_client_hello() -> Result<(), Box<dyn std::error::Error>> {
    let mut rd = rustls::internal::msgs::codec::Reader::init(&BYTES_CLIENT_HELLO_RECORD[9..]);
    let parsed_client_hello = rustls::internal::msgs::handshake::ClientHelloPayload::read(&mut rd)
        .unwrap_or_else(|e| {
            panic!("Failed to parse ClientHello: {:?}", e);
        });
    // println!("parsed_client_hello: {:#?}", parsed_client_hello);

    Ok(())
}

fn parse_vesttls_handshake() -> Result<(), Box<dyn std::error::Error>> {
    for payload in [
        &CLIENT_HELLO_RECORD[5..],
        &SERVER_HELLO_RECORD[5..],
        ENCRTPTED_EXTENSIONS_HANDSHAKE,
        CERTIFICATE_HANDSHAKE,
        CERTIFICATEVERIFY_HANDSHAKE,
        SERVER_FINISHED_HANDSHAKE,
        CLIENT_FINISHED_HANDSHAKE,
    ] {
        let (consumed, parsed_handshake) = handshake().parse(payload).unwrap_or_else(|e| {
            panic!("Failed to parse Handshake: {}", e);
        });
        // println!("consumed: {}", consumed);
        // println!("parsed_handshake: {:#?}", parsed_handshake);
    }

    Ok(())
}

fn parse_rustls_handshake() -> Result<(), Box<dyn std::error::Error>> {
    for payload in [
        &CLIENT_HELLO_RECORD[5..],
        &SERVER_HELLO_RECORD[5..],
        ENCRTPTED_EXTENSIONS_HANDSHAKE,
        CERTIFICATE_HANDSHAKE,
        CERTIFICATEVERIFY_HANDSHAKE,
        SERVER_FINISHED_HANDSHAKE,
        CLIENT_FINISHED_HANDSHAKE,
    ] {
        // let mut rd = rustls::internal::msgs::codec::Reader::init(payload);
        let parsed_handshake = rustls::internal::msgs::message::MessagePayload::new(
            rustls::ContentType::Handshake,
            rustls::ProtocolVersion::TLSv1_3,
            payload,
        )
        .unwrap_or_else(|e| {
            panic!("Failed to parse Handshake: {:?}", e);
        });
        // println!("parsed_handshake: {:#?}", parsed_handshake);
    }

    Ok(())
}

// fn serialize_vesttls_client_hello() -> Result<(), Box<dyn std::error::Error>> {
//     let client_hello_record: ClientHello<'_> = ClientHello {
//         legacy_version: 771,
//         random: &[
//             0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
//             24, 25, 26, 27, 28, 29, 30, 31,
//         ],
//         legacy_session_id: SessionId {
//             l: 32,
//             id: &[
//                 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239,
//                 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255,
//             ],
//         },
//         cipher_suites: CipherSuiteList {
//             l: 8,
//             list: RepeatResult(vec![4866, 4867, 4865, 255]),
//         },
//         legacy_compression_methods: Opaque1Ff { l: 1, data: &[0] },
//         extensions: ClientExtensions {
//             l: 163,
//             extensions: RepeatResult(vec![
//                 ClientHelloExtension {
//                     extension_type: 0,
//                     ext_len: 24,
//                     extension_data: ServerName(ServerNameList {
//                         l: 22,
//                         list: RepeatResult(vec![tls_combinators::ServerName {
//                             name_type: 0,
//                             name: HostName(Opaque1Ffff {
//                                 l: 19,
//                                 data: &[
//                                     101, 120, 97, 109, 112, 108, 101, 46, 117, 108, 102, 104, 101,
//                                     105, 109, 46, 110, 101, 116,
//                                 ],
//                             }),
//                         }]),
//                     }),
//                 },
//                 ClientHelloExtension {
//                     extension_type: 11,
//                     ext_len: 4,
//                     extension_data: ECPointFormats(EcPointFormatList {
//                         l: 3,
//                         list: RepeatResult(vec![0, 1, 2]),
//                     }),
//                 },
//                 ClientHelloExtension {
//                     extension_type: 10,
//                     ext_len: 22,
//                     extension_data: SupportedGroups(NamedGroupList {
//                         l: 20,
//                         list: RepeatResult(vec![29, 23, 30, 25, 24, 256, 257, 258, 259, 260]),
//                     }),
//                 },
//                 ClientHelloExtension {
//                     extension_type: 35,
//                     ext_len: 0,
//                     extension_data: SessionTicket(&[]),
//                 },
//                 ClientHelloExtension {
//                     extension_type: 22,
//                     ext_len: 0,
//                     extension_data: EncryptThenMac(&[]),
//                 },
//                 ClientHelloExtension {
//                     extension_type: 23,
//                     ext_len: 0,
//                     extension_data: ExtendedMasterSecret(&[]),
//                 },
//                 ClientHelloExtension {
//                     extension_type: 13,
//                     ext_len: 30,
//                     extension_data: SignatureAlgorithms(SignatureSchemeList {
//                         l: 28,
//                         list: RepeatResult(vec![
//                             1027, 1283, 1539, 2055, 2056, 2057, 2058, 2059, 2052, 2053, 2054, 1025,
//                             1281, 1537,
//                         ]),
//                     }),
//                 },
//                 ClientHelloExtension {
//                     extension_type: 43,
//                     ext_len: 3,
//                     extension_data: SupportedVersions(SupportedVersionsClient {
//                         l: 2,
//                         versions: RepeatResult(vec![772]),
//                     }),
//                 },
//                 ClientHelloExtension {
//                     extension_type: 45,
//                     ext_len: 2,
//                     extension_data: PskKeyExchangeModes(tls_combinators::PskKeyExchangeModes {
//                         l: 1,
//                         modes: RepeatResult(vec![1]),
//                     }),
//                 },
//                 ClientHelloExtension {
//                     extension_type: 51,
//                     ext_len: 38,
//                     extension_data: KeyShare(KeyShareClientHello {
//                         l: 36,
//                         client_shares: RepeatResult(vec![KeyShareEntry {
//                             group: 29,
//                             l: 32,
//                             key_exchange: X25519(&[
//                                 53, 128, 114, 214, 54, 88, 128, 209, 174, 234, 50, 154, 223, 145,
//                                 33, 56, 56, 81, 237, 33, 162, 142, 59, 117, 233, 101, 208, 210,
//                                 205, 22, 98, 84,
//                             ]),
//                         }]),
//                     }),
//                 },
//             ]),
//         },
//     };
//     let mut outbuf = vec![0u8; 300];
//     let serialized = client_hello()
//         .serialize(client_hello_record, &mut outbuf, 0)
//         .unwrap_or_else(|e| {
//             panic!("Failed to serialize ClientHello: {}", e);
//         });
//     println!("serialized: {}", serialized);
//     println!("serialize_client_hello: {:?}", &outbuf[..serialized]);
//     assert_eq!(
//         &outbuf[..serialized],
//         &BYTES_CLIENT_HELLO_RECORD[9..9 + serialized]
//     );
//
//     Ok(())
// }

// fn client_hello_serialize_parse_roundtrip() -> Result<(), Box<dyn std::error::Error>> {
//     // construct a contrived ClientHello message
//     let client_hello_msg = ClientHello {
//         legacy_version: 0x0303,
//         random: &[0; 32],
//         legacy_session_id: SessionId { l: 0, id: &[] },
//         cipher_suites: CipherSuiteList {
//             l: 2,
//             list: RepeatResult(vec![0x1301]),
//         },
//         legacy_compression_methods: Opaque1Ff { l: 1, data: &[0] },
//         extensions: ClientExtensions {
//             l: 10,
//             extensions: RepeatResult(vec![
//                 ClientHelloExtension {
//                     extension_type: 15,
//                     ext_len: 1,
//                     extension_data: ClientHelloExtensionExtensionData::Heartbeat(1),
//                 },
//                 ClientHelloExtension {
//                     extension_type: 1,
//                     ext_len: 1,
//                     extension_data: ClientHelloExtensionExtensionData::MaxFragmentLength(0),
//                 },
//             ]),
//         },
//     };
//
//     println!(
//         "Size of ClientHello: {}",
//         std::mem::size_of::<ClientHello>()
//     );
//
//     println!("client_hello_msg: {:#?}", client_hello_msg);
//
//     // serialize the ClientHello message
//     let mut buf = vec![0; 53];
//     let len = client_hello()
//         .serialize(client_hello_msg.clone(), &mut buf, 0)
//         .unwrap_or_else(|e| {
//             panic!("Failed to serialize ClientHello: {}", e);
//         });
//
//     println!("len: {}", len);
//     println!("buf: {:?}", buf);
//
//     // parse the serialized ClientHello message
//     let (consumed, parsed_client_hello_msg) =
//         client_hello().parse(&buf[..len]).unwrap_or_else(|e| {
//             panic!("Failed to parse ClientHello: {}", e);
//         });
//
//     // check if the parsed ClientHello message is the same as the original one
//     assert_eq!(len, consumed);
//     println!("parsed_client_hello: {:#?}", parsed_client_hello_msg);
//     assert_eq!(client_hello_msg, parsed_client_hello_msg);
//
//     Ok(())
// }
//
// fn client_hello_parse_serialize_roundtrip() -> Result<(), Box<dyn std::error::Error>> {
//     let input = &[
//         3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
//         0, 0, 0, 0, 0, 0, 2, 19, 1, 1, 0, 0, 10, 0, 15, 0, 1, 1, 0, 1, 0, 1, 0,
//     ];
//
//     let (consumed, parsed_client_hello) = client_hello().parse(input).unwrap_or_else(|e| {
//         panic!("Failed to parse ClientHello: {}", e);
//     });
//
//     println!("consumed: {}", consumed);
//
//     let mut buf = vec![0; 63];
//     let len = client_hello()
//         .serialize(parsed_client_hello, &mut buf, 10)
//         .unwrap_or_else(|e| {
//             panic!("Failed to serialize ClientHello: {}", e);
//         });
//
//     // check if the buf is the same as the original input
//
//     assert_eq!(len, consumed);
//     assert_eq!(buf[10..(len + 10)], input[0..len]);
//
//     Ok(())
// }

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // client_hello_serialize_parse_roundtrip()?;
    // client_hello_parse_serialize_roundtrip()?;
    // parse_vesttls_client_hello()?;
    // parse_rustls_client_hello()?;
    // parse_vesttls_handshake()?;
    // parse_rustls_handshake()?;
    // serialize_vesttls_client_hello()?;
    // bench_fn(parse_rustls_client_hello)?;
    // bench_fn(parse_vesttls_client_hello)?;
    bench_fn(parse_rustls_handshake)?;
    bench_fn(parse_vesttls_handshake)?;

    Ok(())
}

fn bench_fn(
    f: impl Fn() -> Result<(), Box<dyn std::error::Error>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let start = std::time::Instant::now();
    for _ in 0..1000000 {
        f()?;
    }
    println!("Time elapsed: {} ms", start.elapsed().as_millis());

    Ok(())
}
