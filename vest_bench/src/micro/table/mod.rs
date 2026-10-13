//! Table microformat and its matching hand-written codec.

#[rustfmt::skip]
pub mod generated;

pub use generated::TableFmt as Format;
use generated::*;
pub type Value<'a> = Table<'a>;

use super::{Corpus, TABLE_COUNT, TABLE_ENTRIES};

pub struct HandEntry<'a> {
    pub key: &'a [u8],
    pub value_len: u32,
    pub value: &'a [u8],
}

pub struct Hand<'a> {
    pub id: u64,
    pub entry_count: u32,
    pub entries: Vec<HandEntry<'a>>,
}

pub fn parse(b: &[u8]) -> Option<(usize, Hand<'_>)> {
    if b.len() < 12 {
        return None;
    }
    let id = u64::from_be_bytes(b[0..8].try_into().unwrap());
    let entry_count = u32::from_be_bytes(b[8..12].try_into().unwrap());
    let mut pos = 12;
    // Bounded by the remaining input for the same reason the generated parser
    // is: the count is attacker-controlled.
    let cap = (entry_count as usize).min(b.len());
    let mut entries = Vec::with_capacity(cap);
    for _ in 0..entry_count {
        if b.len() < pos + 36 {
            return None;
        }
        let key = &b[pos..pos + 32];
        let value_len = u32::from_be_bytes(b[pos + 32..pos + 36].try_into().unwrap());
        pos += 36;
        let end = pos.checked_add(value_len as usize)?;
        if b.len() < end {
            return None;
        }
        entries.push(HandEntry {
            key,
            value_len,
            value: &b[pos..end],
        });
        pos = end;
    }
    Some((
        pos,
        Hand {
            id,
            entry_count,
            entries,
        },
    ))
}

pub fn size(v: &Hand<'_>) -> Option<usize> {
    if v.entries.len() != v.entry_count as usize {
        return None;
    }
    let mut n = 8 + 4;
    for e in &v.entries {
        if e.key.len() != 32 || e.value.len() != e.value_len as usize {
            return None;
        }
        n += 32 + 4 + e.value.len();
    }
    Some(n)
}

pub fn write(v: &Hand<'_>, out: &mut [u8]) {
    out[0..8].copy_from_slice(&v.id.to_be_bytes());
    out[8..12].copy_from_slice(&v.entry_count.to_be_bytes());
    let mut pos = 12;
    for e in &v.entries {
        out[pos..pos + 32].copy_from_slice(e.key);
        pos += 32;
        out[pos..pos + 4].copy_from_slice(&e.value_len.to_be_bytes());
        pos += 4;
        let end = pos + e.value.len();
        out[pos..end].copy_from_slice(e.value);
        pos = end;
    }
}

pub fn values(corpus: &Corpus) -> Vec<Value<'_>> {
    (0..TABLE_COUNT)
        .map(|t| Table {
            id: t as u64,
            entry_count: TABLE_ENTRIES as u32,
            entries: (0..TABLE_ENTRIES)
                .map(|j| {
                    let k = t * TABLE_ENTRIES + j;
                    TableEntry {
                        key: &corpus.entry_keys[k],
                        value_len: corpus.entry_values[k].len() as u32,
                        value: &corpus.entry_values[k],
                    }
                })
                .collect(),
        })
        .collect()
}

const _: () = super::same_layout::<Value<'static>, Hand<'static>>();
const _: () = super::same_layout::<TableEntry<'static>, HandEntry<'static>>();
