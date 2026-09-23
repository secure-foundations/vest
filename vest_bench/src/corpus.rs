//! Deterministic test data shared by the benchmarks and the wire-compatibility
//! tests.
//!
//! The corpus owns all byte storage; the `*_values` methods hand out borrowed
//! Vest values pointing into it, which is how a real caller would build them.

use crate::bits::{BitsHeader, BitsPacket};
use crate::bounded_list::{BoundedItem, BoundedList};
use crate::tail_list::TailItem;
use crate::flat::FlatRecord;
use crate::nest::{Nest0, Nest1, Nest2, Nest3, Nest4, Nest5, Nest6, Nest7, Nest8};
use crate::table::{Table, TableEntry};
use crate::tlv::{TlvAddr, TlvData, TlvKind, TlvMsg, TlvMsgBody, TlvPing};
use crate::varint::{VarintItem, VarintList};

/// Element counts, kept in one place so the harness and the tests agree.
pub const FLAT_COUNT: usize = 10_000;
pub const TABLE_COUNT: usize = 1_000;
pub const TABLE_ENTRIES: usize = 10;
pub const NEST_COUNT: usize = 10_000;
pub const TLV_COUNT: usize = 10_000;
pub const VARINT_LISTS: usize = 2_000;
pub const VARINT_ITEMS: usize = 16;
pub const BITS_COUNT: usize = 20_000;
pub const LIST_COUNT: usize = 5_000;
pub const LIST_ITEMS: usize = 12;

/// Reproducible LCG, so every run measures the same bytes.
struct Rng(u32);

impl Rng {
    fn next(&mut self, modulus: u32) -> u32 {
        self.0 = self.0.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        (self.0 >> 8) % modulus
    }
}

/// Owned backing storage for every format's test data.
pub struct Corpus {
    keys: Vec<[u8; 32]>,
    payloads: Vec<Vec<u8>>,
    entry_keys: Vec<[u8; 32]>,
    entry_values: Vec<Vec<u8>>,
    nest_payloads: Vec<Vec<u8>>,
    tlv_bodies: Vec<Vec<u8>>,
    varint_data: Vec<Vec<u8>>,
    addrs: Vec<[u8; 4]>,
    list_bodies: Vec<Vec<u8>>,
}

impl Default for Corpus {
    fn default() -> Self {
        Self::new()
    }
}

impl Corpus {
    pub fn new() -> Self {
        let mut rng = Rng(0x1234_5678);
        let keys = (0..FLAT_COUNT).map(|i| [i as u8; 32]).collect();
        let payloads = (0..FLAT_COUNT)
            .map(|_| vec![0xab; (16 + rng.next(240)) as usize])
            .collect();

        let total_entries = TABLE_COUNT * TABLE_ENTRIES;
        let entry_keys = (0..total_entries).map(|i| [i as u8; 32]).collect();
        let entry_values = (0..total_entries)
            .map(|_| vec![0xcd; (16 + rng.next(112)) as usize])
            .collect();

        let nest_payloads = (0..NEST_COUNT).map(|_| vec![0xef; 128]).collect();
        // Sized so `TlvData`'s `Tail` body is non-trivial but bounded.
        let tlv_bodies = (0..TLV_COUNT)
            .map(|_| vec![0x5a; (4 + rng.next(60)) as usize])
            .collect();
        let varint_data = (0..VARINT_LISTS * VARINT_ITEMS)
            .map(|_| vec![0x77; (1 + rng.next(200)) as usize])
            .collect();
        let addrs = (0..TLV_COUNT).map(|i| [10, 0, (i >> 8) as u8, i as u8]).collect();

        let list_bodies = (0..LIST_COUNT * LIST_ITEMS)
            .map(|_| vec![0x33; (1 + rng.next(48)) as usize])
            .collect();
        Self {
            keys,
            payloads,
            entry_keys,
            entry_values,
            nest_payloads,
            tlv_bodies,
            varint_data,
            addrs,
            list_bodies,
        }
    }

    // ---- flat ----

    pub fn flat_values(&self) -> Vec<FlatRecord<'_>> {
        (0..FLAT_COUNT)
            .map(|i| FlatRecord {
                id: i as u64,
                key: &self.keys[i],
                payload_len: self.payloads[i].len() as u32,
                payload: &self.payloads[i],
            })
            .collect()
    }

    // ---- repeat ----

    pub fn table_values(&self) -> Vec<Table<'_>> {
        (0..TABLE_COUNT)
            .map(|t| Table {
                id: t as u64,
                entry_count: TABLE_ENTRIES as u32,
                entries: (0..TABLE_ENTRIES)
                    .map(|j| {
                        let k = t * TABLE_ENTRIES + j;
                        TableEntry {
                            key: &self.entry_keys[k],
                            value_len: self.entry_values[k].len() as u32,
                            value: &self.entry_values[k],
                        }
                    })
                    .collect(),
            })
            .collect()
    }

    // ---- nest ----

    pub fn nest_values(&self) -> Vec<Nest8<'_>> {
        (0..NEST_COUNT)
            .map(|i| {
                let l0 = Nest0 { id: i as u64, len: 128, payload: &self.nest_payloads[i] };
                let l1 = Nest1 { hdr: 0xA7, inner: l0, ftr: 0xB7 };
                let l2 = Nest2 { hdr: 0xA6, inner: l1, ftr: 0xB6 };
                let l3 = Nest3 { hdr: 0xA5, inner: l2, ftr: 0xB5 };
                let l4 = Nest4 { hdr: 0xA4, inner: l3, ftr: 0xB4 };
                let l5 = Nest5 { hdr: 0xA3, inner: l4, ftr: 0xB3 };
                let l6 = Nest6 { hdr: 0xA2, inner: l5, ftr: 0xB2 };
                let l7 = Nest7 { hdr: 0xA1, inner: l6, ftr: 0xB1 };
                Nest8 { hdr: 0xA0, inner: l7, ftr: 0xB0 }
            })
            .collect()
    }

    // ---- tlv ----

    /// Cycles through the three variants so the dispatch is not predictable
    /// from a single branch.
    pub fn tlv_values(&self) -> Vec<TlvMsg<'_>> {
        (0..TLV_COUNT)
            .map(|i| match i % 3 {
                0 => TlvMsg {
                    kind: TlvKind::Ping,
                    len: 8,
                    body: TlvMsgBody::Ping(TlvPing { nonce: i as u64 }),
                },
                1 => {
                    let body = &self.tlv_bodies[i];
                    TlvMsg {
                        kind: TlvKind::Data,
                        len: (4 + body.len()) as u16,
                        body: TlvMsgBody::Data(TlvData { seq: i as u32, body }),
                    }
                }
                _ => TlvMsg {
                    kind: TlvKind::Addr,
                    len: 6,
                    body: TlvMsgBody::Addr(TlvAddr { host: &self.addrs[i], port: i as u16 }),
                },
            })
            .collect()
    }

    // ---- varint ----

    pub fn varint_values(&self) -> Vec<VarintList<'_>> {
        (0..VARINT_LISTS)
            .map(|l| VarintList {
                count: VARINT_ITEMS as u64,
                items: (0..VARINT_ITEMS)
                    .map(|j| {
                        let k = l * VARINT_ITEMS + j;
                        VarintItem {
                            len: self.varint_data[k].len() as u64,
                            data: &self.varint_data[k],
                        }
                    })
                    .collect(),
            })
            .collect()
    }

    // ---- bits ----

    pub fn bits_values(&self) -> Vec<BitsPacket<'_>> {
        (0..BITS_COUNT)
            .map(|i| BitsPacket {
                hdr: BitsHeader { version: 4, ihl: 5, dscp: (i % 64) as u8, ecn: (i % 4) as u8 },
                total_len: 1500,
                ident: i as u16,
                ttl: 64,
                proto: 6,
                checksum: 0xbeef,
                src: &self.addrs[i % self.addrs.len()],
                dst: &self.addrs[(i + 1) % self.addrs.len()],
            })
            .collect()
    }

    // ---- list ----

    fn bounded_items(&self, l: usize) -> Vec<BoundedItem<'_>> {
        (0..LIST_ITEMS)
            .map(|j| {
                let k = l * LIST_ITEMS + j;
                BoundedItem {
                    tag: (j as u16) + 1,
                    len: self.list_bodies[k].len() as u16,
                    body: &self.list_bodies[k],
                }
            })
            .collect()
    }

    pub fn bounded_list_values(&self) -> Vec<BoundedList<'_>> {
        (0..LIST_COUNT)
            .map(|l| {
                let items = self.bounded_items(l);
                let byte_len: usize = items.iter().map(|i| 4 + i.body.len()).sum();
                BoundedList { byte_len: byte_len as u32, items }
            })
            .collect()
    }

    pub fn tail_list_values(&self) -> Vec<Vec<TailItem<'_>>> {
        (0..LIST_COUNT)
            .map(|l| {
                (0..LIST_ITEMS)
                    .map(|j| {
                        let k = l * LIST_ITEMS + j;
                        TailItem {
                            tag: (j as u16) + 1,
                            len: self.list_bodies[k].len() as u16,
                            body: &self.list_bodies[k],
                        }
                    })
                    .collect()
            })
            .collect()
    }

}
