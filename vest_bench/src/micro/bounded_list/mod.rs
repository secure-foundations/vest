//! Bounded list microformat and its matching hand-written codec.

#[rustfmt::skip]
pub mod generated;

pub use generated::BoundedListFmt as Format;
use generated::*;
pub type Value<'a> = BoundedList<'a>;

use super::{Corpus, LIST_COUNT, LIST_ITEMS};

/// Matches the generated `BoundedItem`'s field layout.
pub struct HandItem<'a> {
    pub tag: u16,
    pub len: u16,
    pub body: &'a [u8],
}

/// Parses items back to back until `b` is exactly consumed.
fn parse_items(b: &[u8]) -> Option<Vec<HandItem<'_>>> {
    // Each item is at least 4 bytes, which bounds the element count.
    let mut items = Vec::with_capacity(b.len() / 4);
    let mut pos = 0;
    while pos < b.len() {
        if b.len() < pos + 4 {
            return None;
        }
        let tag = u16::from_be_bytes(b[pos..pos + 2].try_into().unwrap());
        let len = u16::from_be_bytes(b[pos + 2..pos + 4].try_into().unwrap());
        pos += 4;
        let end = pos.checked_add(len as usize)?;
        if b.len() < end {
            return None;
        }
        items.push(HandItem {
            tag,
            len,
            body: &b[pos..end],
        });
        pos = end;
    }
    Some(items)
}

pub struct Hand<'a> {
    pub byte_len: u32,
    pub items: Vec<HandItem<'a>>,
}

pub fn parse(b: &[u8]) -> Option<(usize, Hand<'_>)> {
    if b.len() < 4 {
        return None;
    }
    let byte_len = u32::from_be_bytes(b[0..4].try_into().unwrap());
    let end = 4usize.checked_add(byte_len as usize)?;
    if b.len() < end {
        return None;
    }
    let items = parse_items(&b[4..end])?;
    Some((end, Hand { byte_len, items }))
}

pub fn size(v: &Hand<'_>) -> Option<usize> {
    let mut inner = 0usize;
    for i in &v.items {
        if i.body.len() != i.len as usize {
            return None;
        }
        inner += 4 + i.body.len();
    }
    if inner != v.byte_len as usize {
        return None;
    }
    Some(4 + inner)
}

pub fn write(v: &Hand<'_>, out: &mut [u8]) {
    out[0..4].copy_from_slice(&v.byte_len.to_be_bytes());
    let mut pos = 4;
    for i in &v.items {
        out[pos..pos + 2].copy_from_slice(&i.tag.to_be_bytes());
        out[pos + 2..pos + 4].copy_from_slice(&i.len.to_be_bytes());
        pos += 4;
        let end = pos + i.body.len();
        out[pos..end].copy_from_slice(i.body);
        pos = end;
    }
}

fn items(corpus: &Corpus, l: usize) -> Vec<BoundedItem<'_>> {
    (0..LIST_ITEMS)
        .map(|j| {
            let k = l * LIST_ITEMS + j;
            BoundedItem {
                tag: (j as u16) + 1,
                len: corpus.list_bodies[k].len() as u16,
                body: &corpus.list_bodies[k],
            }
        })
        .collect()
}

pub fn values(corpus: &Corpus) -> Vec<Value<'_>> {
    (0..LIST_COUNT)
        .map(|l| {
            let items = items(corpus, l);
            let byte_len: usize = items.iter().map(|i| 4 + i.body.len()).sum();
            BoundedList {
                byte_len: byte_len as u32,
                items,
            }
        })
        .collect()
}

const _: () = super::same_layout::<Value<'static>, Hand<'static>>();
const _: () = super::same_layout::<BoundedItem<'static>, HandItem<'static>>();
