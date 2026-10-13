//! Captured mainnet blocks in manifest order.

use super::{corpora_dir, tsv_rows};
use bitcoin::consensus::{Decodable, Encodable};
use std::fs;
use vest_tests::bitcoin::BlockFmt;

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

pub struct Values<'i> {
    pub vest: Vec<vest_tests::bitcoin::Block<'i>>,
    pub bitcoin: Vec<bitcoin::Block>,
}

/// Parse once, require full consumption, and check both encoders byte-for-byte.
pub fn values(inputs: &[Vec<u8>]) -> Values<'_> {
    let mut vest = Vec::new();
    let mut bitcoin = Vec::new();
    for input in inputs {
        vest.push(crate::harness::roundtrip(&BlockFmt, input).unwrap());
        let mut remaining = &input[..];
        let value = bitcoin::Block::consensus_decode(&mut remaining).unwrap();
        assert!(remaining.is_empty());
        assert_eq!(value.total_size(), input.len());
        let mut encoded = Vec::new();
        value.consensus_encode(&mut encoded).unwrap();
        assert_eq!(&encoded, input);
        bitcoin.push(value);
    }
    Values { vest, bitcoin }
}
