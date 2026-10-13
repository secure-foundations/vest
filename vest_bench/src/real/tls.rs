//! Captured TLS traffic, Rustls' owned-input adapter, and byte-preserving checks.
use super::{corpora_dir, tsv_rows};
use base64::prelude::*;
use rustls::internal::msgs::handshake::HandshakeMessagePayload;
use rustls::internal::msgs::message::MessagePayload;
use rustls::internal::msgs::{base::Payload, codec::Codec};
use rustls::{ContentType, ProtocolVersion};
use vest_tests::tls::HandshakeFmt;

/// Which endpoint sent a captured TLS message or record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sender {
    Client,
    Server,
}

/// One handshake message from `corpora/tls/handshakes.tsv`: a `Handshake`
/// structure, header included, as sent (or, after the ServerHello, as
/// decrypted).
#[derive(Clone, Debug)]
pub struct TlsHandshake {
    pub peer: String,
    pub client: String,
    pub sender: Sender,
    /// `client_hello`, `hello_retry_request`, `certificate`, and so on.
    pub message: String,
    pub bytes: Vec<u8>,
}

/// One record from `corpora/tls/records.tsv`, header included: a
/// `TLSPlaintext` record, or a `TLSCiphertext` record once keys are in use.
#[derive(Clone, Debug)]
pub struct TlsRecord {
    pub peer: String,
    pub client: String,
    pub sender: Sender,
    pub bytes: Vec<u8>,
}

fn sender(column: &str) -> Sender {
    match column {
        "client" => Sender::Client,
        "server" => Sender::Server,
        other => panic!("unknown sender `{other}`"),
    }
}

fn base64(column: &str) -> Vec<u8> {
    BASE64_STANDARD.decode(column).expect("valid base64")
}

pub fn tls_handshakes() -> Vec<TlsHandshake> {
    tsv_rows(&corpora_dir().join("tls/handshakes.tsv"), 5)
        .into_iter()
        .map(|row| TlsHandshake {
            peer: row[0].clone(),
            client: row[1].clone(),
            sender: sender(&row[2]),
            message: row[3].clone(),
            bytes: base64(&row[4]),
        })
        .collect()
}

pub fn tls_records() -> Vec<TlsRecord> {
    tsv_rows(&corpora_dir().join("tls/records.tsv"), 4)
        .into_iter()
        .map(|row| TlsRecord {
            peer: row[0].clone(),
            client: row[1].clone(),
            sender: sender(&row[2]),
            bytes: base64(&row[3]),
        })
        .collect()
}

#[inline]
pub fn parse(payload: &mut Payload) -> HandshakeMessagePayload {
    // Restore the encoded buffer to its owner: parsing a borrowed Vest input
    // does not dispose of that input either. The harness retains parsed values
    // until the timer stops; input creation and disposal are also untimed.
    let owned = std::mem::replace(payload, Payload::new(Vec::new()));
    match MessagePayload::new(ContentType::Handshake, ProtocolVersion::TLSv1_3, owned).unwrap() {
        MessagePayload::Handshake { parsed, encoded } => {
            *payload = encoded;
            parsed
        }
        _ => unreachable!(),
    }
}

pub struct Values<'i> {
    pub vest: Vec<vest_tests::tls::Handshake<'i>>,
    pub rustls: Vec<HandshakeMessagePayload>,
}

/// Parse once and check both encoders, returning validated serializer inputs.
pub fn values<'i>(inputs: &'i [Vec<u8>]) -> Values<'i> {
    assert!(!inputs.is_empty(), "no TLS handshakes in the corpus");
    let mut encoded = Vec::new();
    let mut vest = Vec::new();
    let mut rustls = Vec::new();
    for input in inputs {
        let input = &input[..];
        assert!(input.len() >= 4);
        let body_len = u32::from_be_bytes([0, input[1], input[2], input[3]]) as usize;
        assert_eq!(
            body_len + 4,
            input.len(),
            "trailing or incomplete TLS handshake"
        );
        vest.push(crate::harness::roundtrip(&HandshakeFmt, input).unwrap());

        encoded.clear();
        let value = parse(&mut Payload::new(input.to_vec()));
        value.encode(&mut encoded);
        assert_eq!(
            &encoded, input,
            "Rustls re-encodes a TLS handshake differently"
        );
        rustls.push(value);
    }
    Values { vest, rustls }
}
