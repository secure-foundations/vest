//! Loaders for the captured real-world corpora under `corpora/`, shared by the
//! real-format benchmarks and the tests that validate the corpora against the
//! Vest specifications.

use std::fs;
use std::path::{Path, PathBuf};

use base64::prelude::*;

/// Directory holding the checked-in corpora.
pub fn corpora_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("corpora")
}

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

fn tsv_rows(path: &Path, columns: usize) -> Vec<Vec<String>> {
    let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    text.lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .map(|line| {
            let row: Vec<String> = line.split('\t').map(str::to_owned).collect();
            assert_eq!(
                row.len(),
                columns,
                "malformed row in {}: {line}",
                path.display()
            );
            row
        })
        .collect()
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

/// A block from `corpora/bitcoin/`, listed in its `MANIFEST.tsv`.
#[derive(Clone, Debug)]
pub struct BitcoinBlock {
    pub height: u32,
    /// Block hash in the conventional (byte-reversed) hex display order.
    pub hash: String,
    pub bytes: Vec<u8>,
}

pub fn bitcoin_blocks() -> Vec<BitcoinBlock> {
    let dir = corpora_dir().join("bitcoin");
    tsv_rows(&dir.join("MANIFEST.tsv"), 3)
        .into_iter()
        .map(|row| {
            let height: u32 = row[0].parse().expect("block height");
            let path = dir.join(format!("{height}.bin"));
            let bytes = fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            assert_eq!(
                bytes.len().to_string(),
                row[2],
                "size of {}",
                path.display()
            );
            BitcoinBlock {
                height,
                hash: row[1].clone(),
                bytes,
            }
        })
        .collect()
}
