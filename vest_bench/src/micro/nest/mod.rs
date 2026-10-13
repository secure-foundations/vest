//! Nest microformat and its matching hand-written codec.

#[rustfmt::skip]
pub mod generated;

pub use generated::Nest8Fmt as Format;
use generated::*;
pub type Value<'a> = Nest8<'a>;

use super::{Corpus, NEST_COUNT};

// Mirrors the generated `Nest0..Nest8`: the schema nests, so the hand-written
// value nests too. Flattening it here would compare two different data
// structures and flatter the baseline.
pub struct HandNest0<'a> {
    pub id: u64,
    pub len: u32,
    pub payload: &'a [u8],
}

macro_rules! hnest {
    ($name:ident, $inner:ident) => {
        pub struct $name<'a> {
            pub hdr: u32,
            pub inner: $inner<'a>,
            pub ftr: u16,
        }
    };
}

hnest!(HandNest1, HandNest0);
hnest!(HandNest2, HandNest1);
hnest!(HandNest3, HandNest2);
hnest!(HandNest4, HandNest3);
hnest!(HandNest5, HandNest4);
hnest!(HandNest6, HandNest5);
hnest!(HandNest7, HandNest6);
hnest!(Hand, HandNest7);

pub const NEST_DEPTH: usize = 8;

macro_rules! read_hdr {
    ($b:expr, $pos:expr) => {{
        if $b.len() < $pos + 4 {
            return None;
        }
        let h = u32::from_be_bytes($b[$pos..$pos + 4].try_into().unwrap());
        $pos += 4;
        h
    }};
}

macro_rules! read_ftr {
    ($b:expr, $pos:expr) => {{
        if $b.len() < $pos + 2 {
            return None;
        }
        let f = u16::from_be_bytes($b[$pos..$pos + 2].try_into().unwrap());
        $pos += 2;
        f
    }};
}

pub fn parse(b: &[u8]) -> Option<(usize, Hand<'_>)> {
    let mut pos = 0;
    let h8 = read_hdr!(b, pos);
    let h7 = read_hdr!(b, pos);
    let h6 = read_hdr!(b, pos);
    let h5 = read_hdr!(b, pos);
    let h4 = read_hdr!(b, pos);
    let h3 = read_hdr!(b, pos);
    let h2 = read_hdr!(b, pos);
    let h1 = read_hdr!(b, pos);

    if b.len() < pos + 12 {
        return None;
    }
    let id = u64::from_be_bytes(b[pos..pos + 8].try_into().unwrap());
    pos += 8;
    let len = u32::from_be_bytes(b[pos..pos + 4].try_into().unwrap());
    pos += 4;
    let end = pos.checked_add(len as usize)?;
    if b.len() < end {
        return None;
    }
    let l0 = HandNest0 {
        id,
        len,
        payload: &b[pos..end],
    };
    pos = end;

    let f1 = read_ftr!(b, pos);
    let f2 = read_ftr!(b, pos);
    let f3 = read_ftr!(b, pos);
    let f4 = read_ftr!(b, pos);
    let f5 = read_ftr!(b, pos);
    let f6 = read_ftr!(b, pos);
    let f7 = read_ftr!(b, pos);
    let f8 = read_ftr!(b, pos);

    let l1 = HandNest1 {
        hdr: h1,
        inner: l0,
        ftr: f1,
    };
    let l2 = HandNest2 {
        hdr: h2,
        inner: l1,
        ftr: f2,
    };
    let l3 = HandNest3 {
        hdr: h3,
        inner: l2,
        ftr: f3,
    };
    let l4 = HandNest4 {
        hdr: h4,
        inner: l3,
        ftr: f4,
    };
    let l5 = HandNest5 {
        hdr: h5,
        inner: l4,
        ftr: f5,
    };
    let l6 = HandNest6 {
        hdr: h6,
        inner: l5,
        ftr: f6,
    };
    let l7 = HandNest7 {
        hdr: h7,
        inner: l6,
        ftr: f7,
    };
    Some((
        pos,
        Hand {
            hdr: h8,
            inner: l7,
            ftr: f8,
        },
    ))
}

pub fn size(v: &Hand<'_>) -> Option<usize> {
    let l0 = &v.inner.inner.inner.inner.inner.inner.inner.inner;
    if l0.payload.len() != l0.len as usize {
        return None;
    }
    Some(NEST_DEPTH * 6 + 8 + 4 + l0.payload.len())
}

pub fn write(v: &Hand<'_>, out: &mut [u8]) {
    let l7 = &v.inner;
    let l6 = &l7.inner;
    let l5 = &l6.inner;
    let l4 = &l5.inner;
    let l3 = &l4.inner;
    let l2 = &l3.inner;
    let l1 = &l2.inner;
    let l0 = &l1.inner;
    let mut pos = 0;
    for h in [
        v.hdr, l7.hdr, l6.hdr, l5.hdr, l4.hdr, l3.hdr, l2.hdr, l1.hdr,
    ] {
        out[pos..pos + 4].copy_from_slice(&h.to_be_bytes());
        pos += 4;
    }
    out[pos..pos + 8].copy_from_slice(&l0.id.to_be_bytes());
    pos += 8;
    out[pos..pos + 4].copy_from_slice(&l0.len.to_be_bytes());
    pos += 4;
    let end = pos + l0.payload.len();
    out[pos..end].copy_from_slice(l0.payload);
    pos = end;
    for f in [
        l1.ftr, l2.ftr, l3.ftr, l4.ftr, l5.ftr, l6.ftr, l7.ftr, v.ftr,
    ] {
        out[pos..pos + 2].copy_from_slice(&f.to_be_bytes());
        pos += 2;
    }
}

pub fn values(corpus: &Corpus) -> Vec<Value<'_>> {
    (0..NEST_COUNT)
        .map(|i| {
            let l0 = Nest0 {
                id: i as u64,
                len: 128,
                payload: &corpus.nest_payloads[i],
            };
            let l1 = Nest1 {
                hdr: 0xA7,
                inner: l0,
                ftr: 0xB7,
            };
            let l2 = Nest2 {
                hdr: 0xA6,
                inner: l1,
                ftr: 0xB6,
            };
            let l3 = Nest3 {
                hdr: 0xA5,
                inner: l2,
                ftr: 0xB5,
            };
            let l4 = Nest4 {
                hdr: 0xA4,
                inner: l3,
                ftr: 0xB4,
            };
            let l5 = Nest5 {
                hdr: 0xA3,
                inner: l4,
                ftr: 0xB3,
            };
            let l6 = Nest6 {
                hdr: 0xA2,
                inner: l5,
                ftr: 0xB2,
            };
            let l7 = Nest7 {
                hdr: 0xA1,
                inner: l6,
                ftr: 0xB1,
            };
            Nest8 {
                hdr: 0xA0,
                inner: l7,
                ftr: 0xB0,
            }
        })
        .collect()
}

const _: () = super::same_layout::<Value<'static>, Hand<'static>>();
