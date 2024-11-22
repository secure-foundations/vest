use tls_combinators::*;
use vest::properties::*;
use vest::regular::repeat::RepeatResult;

pub mod tls_combinators;

// pub type ProtocolVersion = u16;
// pub type Random<'a> = &'a [u8];
// pub struct SessionId<'a> {
//     pub l: u8,
//     pub id: &'a [u8],
// }
// pub struct CipherSuiteList {
//     pub l: Uint2Fffe,
//     pub list: CipherSuiteListList,
// }
// pub type CipherSuiteListList = RepeatResult<CipherSuite>;
// pub type CipherSuite = u16;
// pub struct Opaque1Ff<'a> {
//     pub l: Uint1Ff,
//     pub data: &'a [u8],
// }
// pub type Uint1Ff = u8;
// pub struct ClientExtensions<'a> {
//     pub l: u16,
//     pub extensions: ClientExtensionsExtensions<'a>,
// }
// pub type ClientExtensionsExtensions<'a> = RepeatResult<ClientHelloExtension<'a>>;
// pub struct ClientHelloExtension<'a> {
//     pub extension_type: ExtensionType,
//     pub ext_len: u16,
//     pub extension_data: ClientHelloExtensionExtensionData<'a>,
// }
// pub enum ClientHelloExtensionExtensionData<'a> {
//     ServerName(Empty<'a>),
//     MaxFragmentLength(MaxFragmentLength),
//     StatusRequest(Empty<'a>),
//     ECPointFormats(EcPointFormatList),
//     UseSRTP(UseSrtpData<'a>),
//     Heartbeat(HeartbeatMode),
//     ApplicationLayerProtocolNegotiation(ProtocolNameList<'a>),
//     SigedCertificateTimestamp(SignedCertificateTimestampList<'a>),
//     ClientCertificateType(ClientCertTypeClientExtension),
//     ServerCertificateType(ServerCertTypeClientExtension),
//     Padding(PaddingExtension),
//     EncryptThenMac(Empty<'a>),
//     ExtendedMasterSecret(Empty<'a>),
//     SessionTicket(SessionTicket<'a>),
//     PreSharedKey(PreSharedKeyClientExtension<'a>),
//     EarlyData(Empty<'a>),
//     SupportedVersions(SupportedVersionsClient),
//     Cookie(Cookie<'a>),
//     PskKeyExchangeModes(PskKeyExchangeModes),
//     CertificateAuthorities(CertificateAuthoritiesExtension<'a>),
//     OidFilters(OidFilterExtension<'a>),
//     PostHandshakeAuth(Empty<'a>),
//     SignatureAlgorithmsCert(SignatureSchemeList),
//     KeyShare(KeyShareClientHello<'a>),
//     Unrecognized(UnknownExtension<'a>),
// }
// pub type ExtensionType = u8;
// pub struct Opaque0Ffff<'a> {
//     pub l: Uint0Ffff,
//     pub data: &'a [u8],
// }
// pub type Uint0Ffff = u16;
// pub struct ClientHello<'a> {
//     pub legacy_version: ProtocolVersion,
//     pub random: Random<'a>,
//     pub legacy_session_id: SessionId<'a>,
//     pub cipher_suites: CipherSuiteList,
//     pub legacy_compression_methods: Opaque1Ff<'a>,
//     pub extensions: ClientExtensions<'a>,
// }

fn client_hello_serialize_parse_roundtrip() -> Result<(), Box<dyn std::error::Error>> {
    // construct a contrived ClientHello message
    let client_hello_msg = ClientHello {
        legacy_version: 0x0303,
        random: &[0; 32],
        legacy_session_id: SessionId { l: 0, id: &[] },
        cipher_suites: CipherSuiteList {
            l: 2,
            list: RepeatResult(vec![0x1301]),
        },
        legacy_compression_methods: Opaque1Ff { l: 1, data: &[0] },
        extensions: ClientExtensions {
            l: 8,
            extensions: RepeatResult(vec![
                ClientHelloExtension {
                    extension_type: 15,
                    ext_len: 1,
                    extension_data: ClientHelloExtensionExtensionData::Heartbeat(1),
                },
                ClientHelloExtension {
                    extension_type: 1,
                    ext_len: 1,
                    extension_data: ClientHelloExtensionExtensionData::MaxFragmentLength(0),
                },
            ]),
        },
    };

    println!(
        "Size of ClientHello: {}",
        std::mem::size_of::<ClientHello>()
    );

    println!("client_hello_msg: {:#?}", client_hello_msg);

    // serialize the ClientHello message
    let mut buf = vec![0; 51];
    let len = client_hello()
        .serialize(client_hello_msg.clone(), &mut buf, 0)
        .unwrap_or_else(|e| {
            panic!("Failed to serialize ClientHello: {}", e);
        });

    println!("len: {}", len);
    println!("buf: {:?}", buf);

    // parse the serialized ClientHello message
    let (consumed, parsed_client_hello_msg) =
        client_hello().parse(&buf[..len]).unwrap_or_else(|e| {
            panic!("Failed to parse ClientHello: {}", e);
        });

    // check if the parsed ClientHello message is the same as the original one
    assert_eq!(len, consumed);
    println!("parsed_client_hello: {:#?}", parsed_client_hello_msg);
    assert_eq!(client_hello_msg, parsed_client_hello_msg);

    Ok(())
}

fn client_hello_parse_serialize_roundtrip() -> Result<(), Box<dyn std::error::Error>> {
    let input = &[
        3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 2, 19, 1, 1, 0, 0, 8, 15, 0, 1, 1, 1, 0, 1, 0,
    ];

    let (consumed, parsed_client_hello) = client_hello().parse(input).unwrap_or_else(|e| {
        panic!("Failed to parse ClientHello: {}", e);
    });

    println!("consumed: {}", consumed);

    let mut buf = vec![0; 61];
    let len = client_hello()
        .serialize(parsed_client_hello, &mut buf, 10)
        .unwrap_or_else(|e| {
            panic!("Failed to serialize ClientHello: {}", e);
        });

    // check if the buf is the same as the original input

    assert_eq!(len, consumed);
    assert_eq!(buf[10..(len + 10)], input[0..len]);

    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    client_hello_serialize_parse_roundtrip()?;
    client_hello_parse_serialize_roundtrip()?;

    Ok(())
}
