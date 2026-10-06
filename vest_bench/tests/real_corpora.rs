//! The real-format corpora are captured protocol traffic, so parsing them
//! checks the Vest specifications against deployed implementations: every
//! message must be accepted, consume exactly its bytes, and serialize back to
//! the same bytes. The Bitcoin blocks are also checked against rust-bitcoin.

use bitcoin::consensus::Decodable;
use vest_bench::real::{self, Sender};
use vest_lib::core::exec::parser::Parser;
use vest_lib::core::exec::serializer::{Prepare, SerializerExt};
use vest_tests::bitcoin::{BlockFmt, TxPayload};
use vest_tests::tls::{
    ClientHelloExtensionData, HandshakeFmt, HandshakeMsg, ServerHelloExtensionData, ShOrHrrPayload,
    TlsCiphertextFmt, TlsPlaintextFmt, TlsPlaintextFragment,
};

/// Parses `bytes` with `fmt`, requires that the parse consume every byte and
/// that serializing the result reproduce `bytes`, and yields the value.
macro_rules! roundtrip {
    ($fmt:expr, $bytes:expr) => {{
        let bytes: &[u8] = $bytes;
        match $fmt.parse(&bytes) {
            Err(e) => Err(format!("rejected: {e}")),
            Ok((n, _)) if n != bytes.len() => Err(format!("consumed {n} of {} bytes", bytes.len())),
            Ok((_, value)) => match $fmt.prepare(&value) {
                Err(e) => Err(format!("prepare failed: {e:?}")),
                Ok(len) => {
                    let mut out = vec![0; len];
                    $fmt.serialize(&value, out.as_mut_slice());
                    if out == bytes {
                        Ok(value)
                    } else {
                        Err("serialized bytes differ".to_owned())
                    }
                }
            },
        }
    }};
}

fn assert_no_failures(what: &str, total: usize, failures: Vec<String>) {
    assert!(total > 0, "the {what} corpus is empty");
    assert!(
        failures.is_empty(),
        "{} of {total} {what} failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn tls_handshake_messages_roundtrip() {
    let corpus = real::tls_handshakes();
    let mut failures = Vec::new();
    for (i, m) in corpus.iter().enumerate() {
        let label = format!(
            "#{i} {} {} {} {}",
            m.peer,
            m.client,
            m.message,
            m.bytes.len()
        );
        match roundtrip!(HandshakeFmt, &m.bytes) {
            Err(e) => failures.push(format!("{label}: {e}")),
            Ok(value) => {
                let parsed = match &value.msg {
                    HandshakeMsg::ClientHello(_) => "client_hello",
                    HandshakeMsg::ServerHello(sh) => match sh.payload {
                        ShOrHrrPayload::HelloRetryRequest(_) => "hello_retry_request",
                        ShOrHrrPayload::ServerHello(_) => "server_hello",
                    },
                    HandshakeMsg::NewSessionTicket(_) => "new_session_ticket",
                    HandshakeMsg::EndOfEarlyData(_) => "end_of_early_data",
                    HandshakeMsg::EncryptedExtensions(_) => "encrypted_extensions",
                    HandshakeMsg::Certificate(_) => "certificate",
                    HandshakeMsg::CertificateRequest(_) => "certificate_request",
                    HandshakeMsg::CertificateVerify(_) => "certificate_verify",
                    HandshakeMsg::Finished(_) => "finished",
                    HandshakeMsg::KeyUpdate(_) => "key_update",
                };
                if parsed != m.message {
                    failures.push(format!("{label}: parsed as {parsed}"));
                }
                let from_server = !matches!(value.msg, HandshakeMsg::ClientHello(_));
                if from_server != (m.sender == Sender::Server) && parsed != "finished" {
                    failures.push(format!("{label}: sent by the wrong endpoint"));
                }
            }
        }
    }
    assert_no_failures("TLS handshake messages", corpus.len(), failures);
}

#[test]
fn tls_records_roundtrip() {
    let corpus = real::tls_records();
    let mut failures = Vec::new();
    for (i, r) in corpus.iter().enumerate() {
        let label = format!(
            "#{i} {} {} {:?} {}",
            r.peer,
            r.client,
            r.sender,
            r.bytes.len()
        );
        // Once keys are in use, every record's outer content type is
        // application_data (RFC 9846 Section 5.2); earlier records are plain.
        let result = if r.bytes[0] == 23 {
            roundtrip!(TlsCiphertextFmt, &r.bytes).map(|_| ())
        } else {
            roundtrip!(TlsPlaintextFmt, &r.bytes).and_then(|record| match record.fragment {
                TlsPlaintextFragment::Handshake(_) | TlsPlaintextFragment::ChangeCipherSpec(_) => {
                    Ok(())
                }
                TlsPlaintextFragment::Alert(alert) => Err(format!("plaintext alert {alert:?}")),
                other => Err(format!("unexpected plaintext fragment {other:?}")),
            })
        };
        if let Err(e) = result {
            failures.push(format!("{label}: {e}"));
        }
    }
    assert_no_failures("TLS records", corpus.len(), failures);
}

#[test]
fn bitcoin_blocks_roundtrip_and_agree_with_rust_bitcoin() {
    let corpus = real::bitcoin_blocks();
    let mut failures = Vec::new();
    for b in &corpus {
        let label = format!("block {}", b.height);
        let reference =
            bitcoin::Block::consensus_decode(&mut &b.bytes[..]).expect("rust-bitcoin decodes");
        // The corpus is authentic: the header hashes to the recorded block
        // hash, and the transactions match the header's commitments.
        assert_eq!(
            reference.block_hash().to_string(),
            b.hash,
            "{label}: block hash"
        );
        assert!(reference.check_merkle_root(), "{label}: merkle root");
        assert!(
            reference.check_witness_commitment(),
            "{label}: witness commitment"
        );

        match roundtrip!(BlockFmt, &b.bytes) {
            Err(e) => failures.push(format!("{label}: {e}")),
            Ok(block) => {
                assert_eq!(
                    block.transactions.len(),
                    reference.txdata.len(),
                    "{label}: tx count"
                );
                for (i, (tx, expected)) in
                    block.transactions.iter().zip(&reference.txdata).enumerate()
                {
                    let (inputs, outputs, witnesses) = match &tx.payload {
                        TxPayload::TxWithWitness(w) => {
                            (w.inputs.len(), w.outputs.len(), Some(&w.witnesses))
                        }
                        TxPayload::TxWithoutWitness(t) => (t.inputs.len(), t.outputs.len(), None),
                    };
                    let expected_witnesses =
                        expected.input.iter().any(|input| !input.witness.is_empty());
                    if inputs != expected.input.len()
                        || outputs != expected.output.len()
                        || witnesses.is_some() != expected_witnesses
                        || witnesses.is_some_and(|ws| {
                            ws.iter()
                                .zip(&expected.input)
                                .any(|(w, input)| w.items.len() != input.witness.len())
                        })
                    {
                        failures.push(format!(
                            "{label}: transaction {i} disagrees with rust-bitcoin"
                        ));
                    }
                }
            }
        }
    }
    assert_no_failures("Bitcoin blocks", corpus.len(), failures);
}

/// The name of an enum value's variant, from its `Debug` rendering.
fn variant(value: &impl std::fmt::Debug) -> String {
    let rendered = format!("{value:?}");
    rendered.split(['(', ' ', '{']).next().unwrap().to_owned()
}

/// Bodies whose precise definitions the checked-in TLS corpus must reach.
const EXPECTED_COVERAGE: &[&str] = &[
    "client_hello/CompressCertificate",
    "client_hello/ECPointFormats",
    "client_hello/EncryptedClientHello",
    "client_hello/encrypted_client_hello/Outer",
    "client_hello/Padding",
    "client_hello/PreSharedKey",
    "client_hello/RenegotiationInfo",
    "client_hello/SignedCertificateTimeStamp",
    "client_hello/StatusRequest",
    "client_hello/key_share/Ffdhe2048",
    "client_hello/key_share/Secp256r1",
    "client_hello/key_share/Secp384r1",
    "client_hello/key_share/Secp521r1",
    "client_hello/key_share/X25519",
    "client_hello/key_share/X448",
    "server_hello/PreSharedKey",
    "server_hello/key_share/Secp256r1",
    "server_hello/key_share/Secp384r1",
    "server_hello/key_share/Secp521r1",
    "server_hello/key_share/X25519",
    "hello_retry_request/KeyShare",
    "encrypted_extensions/ApplicationLayerProtocolNegotiation",
    "encrypted_extensions/ServerName",
    "encrypted_extensions/SupportedGroups",
    "certificate/SignedCertificateTimeStamp",
    "certificate/StatusRequest",
    "new_session_ticket/EarlyData",
];

/// Which extension bodies and key-share encodings the TLS corpus reaches.
/// Without this, a body that fell through to its message's `_ => Tail` arm
/// would still round-trip, and the corpus would validate less than it seems.
#[test]
fn tls_corpus_exercises_the_precise_bodies() {
    use std::collections::BTreeMap;
    let corpus = real::tls_handshakes();
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    let mut note = |key: String| *seen.entry(key).or_default() += 1;
    for m in &corpus {
        let (_, value) = HandshakeFmt.parse(&&m.bytes[..]).unwrap();
        match &value.msg {
            HandshakeMsg::ClientHello(ch) => {
                for ext in &ch.extensions.list {
                    note(format!("client_hello/{}", variant(&ext.data)));
                    match &ext.data {
                        ClientHelloExtensionData::KeyShare(shares) => {
                            for share in &shares.list {
                                note(format!(
                                    "client_hello/key_share/{}",
                                    variant(&share.key_exchange)
                                ));
                            }
                        }
                        ClientHelloExtensionData::EncryptedClientHello(ech) => {
                            note(format!(
                                "client_hello/encrypted_client_hello/{}",
                                variant(&ech.body)
                            ));
                        }
                        _ => {}
                    }
                }
            }
            HandshakeMsg::ServerHello(sh) => match &sh.payload {
                ShOrHrrPayload::ServerHello(sh) => {
                    for ext in &sh.extensions.list {
                        note(format!("server_hello/{}", variant(&ext.data)));
                        if let ServerHelloExtensionData::KeyShare(share) = &ext.data {
                            note(format!(
                                "server_hello/key_share/{}",
                                variant(&share.key_exchange)
                            ));
                        }
                    }
                }
                ShOrHrrPayload::HelloRetryRequest(hrr) => {
                    for ext in &hrr.extensions.list {
                        note(format!("hello_retry_request/{}", variant(&ext.data)));
                    }
                }
            },
            HandshakeMsg::EncryptedExtensions(ee) => {
                for ext in &ee.list {
                    note(format!("encrypted_extensions/{}", variant(&ext.data)));
                }
            }
            HandshakeMsg::Certificate(certificate) => {
                for entry in &certificate.certificate_list.list {
                    for ext in &entry.extensions.list {
                        note(format!("certificate/{}", variant(&ext.data)));
                    }
                }
            }
            HandshakeMsg::NewSessionTicket(ticket) => {
                for ext in &ticket.extensions.list {
                    note(format!("new_session_ticket/{}", variant(&ext.data)));
                }
            }
            _ => {}
        }
    }
    for (key, count) in &seen {
        println!("{count:>5}  {key}");
    }
    let missing: Vec<_> = EXPECTED_COVERAGE
        .iter()
        .filter(|key| !seen.contains_key(**key))
        .collect();
    assert!(
        missing.is_empty(),
        "the TLS corpus no longer reaches {missing:?}"
    );
}
