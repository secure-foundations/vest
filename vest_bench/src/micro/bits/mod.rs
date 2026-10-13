//! Bits microformat and its matching hand-written codec.

#[rustfmt::skip]
pub mod generated;

pub use generated::BitsPacketFmt as Format;
use generated::*;
pub type Value<'a> = BitsPacket<'a>;

use super::{Corpus, BITS_COUNT};

/// Mirrors the generated `BitsHeader`.
pub struct HandHeader {
    pub version: u8,
    pub ihl: u8,
    pub dscp: u8,
    pub ecn: u8,
}

pub struct Hand<'a> {
    pub hdr: HandHeader,
    pub total_len: u16,
    pub ident: u16,
    pub ttl: u8,
    pub proto: u8,
    pub checksum: u16,
    pub src: &'a [u8],
    pub dst: &'a [u8],
}

pub const BITS_SIZE: usize = 2 + 2 + 2 + 1 + 1 + 2 + 4 + 4;

pub fn parse(b: &[u8]) -> Option<(usize, Hand<'_>)> {
    if b.len() < BITS_SIZE {
        return None;
    }
    let hdr = u16::from_be_bytes(b[0..2].try_into().unwrap());
    Some((
        BITS_SIZE,
        Hand {
            hdr: HandHeader {
                version: (hdr & 0xf) as u8,
                ihl: ((hdr >> 4) & 0xf) as u8,
                dscp: ((hdr >> 8) & 0x3f) as u8,
                ecn: ((hdr >> 14) & 0x3) as u8,
            },
            total_len: u16::from_be_bytes(b[2..4].try_into().unwrap()),
            ident: u16::from_be_bytes(b[4..6].try_into().unwrap()),
            ttl: b[6],
            proto: b[7],
            checksum: u16::from_be_bytes(b[8..10].try_into().unwrap()),
            src: &b[10..14],
            dst: &b[14..18],
        },
    ))
}

pub fn size(v: &Hand<'_>) -> Option<usize> {
    if v.src.len() != 4 || v.dst.len() != 4 {
        return None;
    }
    // The bit fields must fit their declared widths.
    if v.hdr.version > 0xf || v.hdr.ihl > 0xf || v.hdr.dscp > 0x3f || v.hdr.ecn > 0x3 {
        return None;
    }
    Some(BITS_SIZE)
}

pub fn write(v: &Hand<'_>, out: &mut [u8]) {
    let hdr = (v.hdr.version as u16 & 0xf)
        | ((v.hdr.ihl as u16 & 0xf) << 4)
        | ((v.hdr.dscp as u16 & 0x3f) << 8)
        | ((v.hdr.ecn as u16 & 0x3) << 14);
    out[0..2].copy_from_slice(&hdr.to_be_bytes());
    out[2..4].copy_from_slice(&v.total_len.to_be_bytes());
    out[4..6].copy_from_slice(&v.ident.to_be_bytes());
    out[6] = v.ttl;
    out[7] = v.proto;
    out[8..10].copy_from_slice(&v.checksum.to_be_bytes());
    out[10..14].copy_from_slice(v.src);
    out[14..18].copy_from_slice(v.dst);
}

pub fn values(corpus: &Corpus) -> Vec<Value<'_>> {
    (0..BITS_COUNT)
        .map(|i| BitsPacket {
            hdr: BitsHeader {
                version: 4,
                ihl: 5,
                dscp: (i % 64) as u8,
                ecn: (i % 4) as u8,
            },
            total_len: 1500,
            ident: i as u16,
            ttl: 64,
            proto: 6,
            checksum: 0xbeef,
            src: &corpus.addrs[i % corpus.addrs.len()],
            dst: &corpus.addrs[(i + 1) % corpus.addrs.len()],
        })
        .collect()
}

const _: () = super::same_layout::<Value<'static>, Hand<'static>>();
