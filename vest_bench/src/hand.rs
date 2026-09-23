//! Hand-written baselines: the fastest correct code a competent engineer would
//! write for each wire format, with no verification machinery.
//!
//! These are the comparison target, so they must be *fair*. Each one performs
//! the same validation the generated parser does — every length is checked
//! against the remaining input, every tag against its domain, and a
//! length-delimited body must be consumed exactly. Parsers borrow rather than
//! copy, matching the generated code, and serializers compute the exact length
//! and then write into a caller-sized buffer.

// ---------------------------------------------------------------- flat

pub struct FlatRef<'a> {
    pub id: u64,
    pub key: &'a [u8],
    pub payload_len: u32,
    pub payload: &'a [u8],
}

pub fn parse_flat(b: &[u8]) -> Option<(usize, FlatRef<'_>)> {
    if b.len() < 44 {
        return None;
    }
    let id = u64::from_be_bytes(b[0..8].try_into().unwrap());
    let key = &b[8..40];
    let payload_len = u32::from_be_bytes(b[40..44].try_into().unwrap());
    let end = 44usize.checked_add(payload_len as usize)?;
    if b.len() < end {
        return None;
    }
    Some((end, FlatRef { id, key, payload_len, payload: &b[44..end] }))
}

pub fn size_flat(v: &FlatRef<'_>) -> Option<usize> {
    if v.key.len() != 32 || v.payload.len() != v.payload_len as usize {
        return None;
    }
    Some(8 + 32 + 4 + v.payload.len())
}

pub fn write_flat(v: &FlatRef<'_>, out: &mut [u8]) {
    out[0..8].copy_from_slice(&v.id.to_be_bytes());
    out[8..40].copy_from_slice(v.key);
    out[40..44].copy_from_slice(&v.payload_len.to_be_bytes());
    out[44..].copy_from_slice(v.payload);
}

// --------------------------------------------------------------- table

pub struct EntryRef<'a> {
    pub key: &'a [u8],
    pub value_len: u32,
    pub value: &'a [u8],
}

pub struct TableRef<'a> {
    pub id: u64,
    pub entry_count: u32,
    pub entries: Vec<EntryRef<'a>>,
}

pub fn parse_table(b: &[u8]) -> Option<(usize, TableRef<'_>)> {
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
        entries.push(EntryRef { key, value_len, value: &b[pos..end] });
        pos = end;
    }
    Some((pos, TableRef { id, entry_count, entries }))
}

pub fn size_table(v: &TableRef<'_>) -> Option<usize> {
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

pub fn write_table(v: &TableRef<'_>, out: &mut [u8]) {
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

// ---------------------------------------------------------------- nest

// Mirrors the generated `Nest0..Nest8`: the schema nests, so the hand-written
// value nests too. Flattening it here would compare two different data
// structures and flatter the baseline.
pub struct HNest0<'a> {
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

hnest!(HNest1, HNest0);
hnest!(HNest2, HNest1);
hnest!(HNest3, HNest2);
hnest!(HNest4, HNest3);
hnest!(HNest5, HNest4);
hnest!(HNest6, HNest5);
hnest!(HNest7, HNest6);
hnest!(HNest8, HNest7);

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

pub fn parse_nest(b: &[u8]) -> Option<(usize, HNest8<'_>)> {
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
    let l0 = HNest0 { id, len, payload: &b[pos..end] };
    pos = end;

    let f1 = read_ftr!(b, pos);
    let f2 = read_ftr!(b, pos);
    let f3 = read_ftr!(b, pos);
    let f4 = read_ftr!(b, pos);
    let f5 = read_ftr!(b, pos);
    let f6 = read_ftr!(b, pos);
    let f7 = read_ftr!(b, pos);
    let f8 = read_ftr!(b, pos);

    let l1 = HNest1 { hdr: h1, inner: l0, ftr: f1 };
    let l2 = HNest2 { hdr: h2, inner: l1, ftr: f2 };
    let l3 = HNest3 { hdr: h3, inner: l2, ftr: f3 };
    let l4 = HNest4 { hdr: h4, inner: l3, ftr: f4 };
    let l5 = HNest5 { hdr: h5, inner: l4, ftr: f5 };
    let l6 = HNest6 { hdr: h6, inner: l5, ftr: f6 };
    let l7 = HNest7 { hdr: h7, inner: l6, ftr: f7 };
    Some((pos, HNest8 { hdr: h8, inner: l7, ftr: f8 }))
}

pub fn size_nest(v: &HNest8<'_>) -> Option<usize> {
    let l0 = &v.inner.inner.inner.inner.inner.inner.inner.inner;
    if l0.payload.len() != l0.len as usize {
        return None;
    }
    Some(NEST_DEPTH * 6 + 8 + 4 + l0.payload.len())
}

pub fn write_nest(v: &HNest8<'_>, out: &mut [u8]) {
    let l7 = &v.inner;
    let l6 = &l7.inner;
    let l5 = &l6.inner;
    let l4 = &l5.inner;
    let l3 = &l4.inner;
    let l2 = &l3.inner;
    let l1 = &l2.inner;
    let l0 = &l1.inner;
    let mut pos = 0;
    for h in [v.hdr, l7.hdr, l6.hdr, l5.hdr, l4.hdr, l3.hdr, l2.hdr, l1.hdr] {
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
    for f in [l1.ftr, l2.ftr, l3.ftr, l4.ftr, l5.ftr, l6.ftr, l7.ftr, v.ftr] {
        out[pos..pos + 2].copy_from_slice(&f.to_be_bytes());
        pos += 2;
    }
}

// ----------------------------------------------------------------- tlv

/// Mirrors the generated `TlvKind`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HTlvKind {
    Ping = 1,
    Data = 2,
    Addr = 3,
}

pub struct HTlvPing {
    pub nonce: u64,
}

pub struct HTlvData<'a> {
    pub seq: u32,
    pub body: &'a [u8],
}

pub struct HTlvAddr<'a> {
    pub host: &'a [u8],
    pub port: u16,
}

pub enum HTlvBody<'a> {
    Ping(HTlvPing),
    Data(HTlvData<'a>),
    Addr(HTlvAddr<'a>),
}

pub struct HTlvMsg<'a> {
    pub kind: HTlvKind,
    pub len: u16,
    pub body: HTlvBody<'a>,
}

pub fn parse_tlv(b: &[u8]) -> Option<(usize, HTlvMsg<'_>)> {
    if b.len() < 3 {
        return None;
    }
    let kind = match b[0] {
        1 => HTlvKind::Ping,
        2 => HTlvKind::Data,
        3 => HTlvKind::Addr,
        _ => return None,
    };
    let len = u16::from_be_bytes(b[1..3].try_into().unwrap());
    let end = 3usize.checked_add(len as usize)?;
    if b.len() < end {
        return None;
    }
    // The body is length-delimited: the variant must consume it exactly, which
    // is what `[u8; @len] >>= choose(..)` means.
    let body_bytes = &b[3..end];
    let body = match kind {
        HTlvKind::Ping => {
            if body_bytes.len() != 8 {
                return None;
            }
            HTlvBody::Ping(HTlvPing { nonce: u64::from_be_bytes(body_bytes[0..8].try_into().unwrap()) })
        }
        HTlvKind::Data => {
            if body_bytes.len() < 4 {
                return None;
            }
            HTlvBody::Data(HTlvData {
                seq: u32::from_be_bytes(body_bytes[0..4].try_into().unwrap()),
                body: &body_bytes[4..],
            })
        }
        HTlvKind::Addr => {
            if body_bytes.len() != 6 {
                return None;
            }
            HTlvBody::Addr(HTlvAddr {
                host: &body_bytes[0..4],
                port: u16::from_be_bytes(body_bytes[4..6].try_into().unwrap()),
            })
        }
    };
    Some((end, HTlvMsg { kind, len, body }))
}

pub fn size_tlv(v: &HTlvMsg<'_>) -> Option<usize> {
    let body = match (&v.body, v.kind) {
        (HTlvBody::Ping(_), HTlvKind::Ping) => 8,
        (HTlvBody::Data(d), HTlvKind::Data) => 4 + d.body.len(),
        (HTlvBody::Addr(a), HTlvKind::Addr) => {
            if a.host.len() != 4 {
                return None;
            }
            6
        }
        // The tag must agree with the variant, as `choose(@kind)` requires.
        _ => return None,
    };
    if body != v.len as usize {
        return None;
    }
    Some(3 + body)
}

pub fn write_tlv(v: &HTlvMsg<'_>, out: &mut [u8]) {
    out[0] = v.kind as u8;
    out[1..3].copy_from_slice(&v.len.to_be_bytes());
    match &v.body {
        HTlvBody::Ping(p) => out[3..11].copy_from_slice(&p.nonce.to_be_bytes()),
        HTlvBody::Data(d) => {
            out[3..7].copy_from_slice(&d.seq.to_be_bytes());
            out[7..].copy_from_slice(d.body);
        }
        HTlvBody::Addr(a) => {
            out[3..7].copy_from_slice(a.host);
            out[7..9].copy_from_slice(&a.port.to_be_bytes());
        }
    }
}

// -------------------------------------------------------------- varint

/// Bitcoin `CompactSize`, rejecting non-minimal encodings the way the
/// generated parser does.
pub fn parse_varint(b: &[u8]) -> Option<(usize, u64)> {
    let first = *b.first()?;
    match first {
        0..=0xfc => Some((1, first as u64)),
        0xfd => {
            if b.len() < 3 {
                return None;
            }
            let v = u16::from_le_bytes(b[1..3].try_into().unwrap()) as u64;
            if v < 0xfd {
                return None;
            }
            Some((3, v))
        }
        0xfe => {
            if b.len() < 5 {
                return None;
            }
            let v = u32::from_le_bytes(b[1..5].try_into().unwrap()) as u64;
            if v <= 0xffff {
                return None;
            }
            Some((5, v))
        }
        _ => {
            if b.len() < 9 {
                return None;
            }
            let v = u64::from_le_bytes(b[1..9].try_into().unwrap());
            if v <= 0xffff_ffff {
                return None;
            }
            Some((9, v))
        }
    }
}

pub fn varint_len(v: u64) -> usize {
    match v {
        0..=0xfc => 1,
        0xfd..=0xffff => 3,
        0x1_0000..=0xffff_ffff => 5,
        _ => 9,
    }
}

pub fn write_varint(v: u64, out: &mut [u8]) -> usize {
    match v {
        0..=0xfc => {
            out[0] = v as u8;
            1
        }
        0xfd..=0xffff => {
            out[0] = 0xfd;
            out[1..3].copy_from_slice(&(v as u16).to_le_bytes());
            3
        }
        0x1_0000..=0xffff_ffff => {
            out[0] = 0xfe;
            out[1..5].copy_from_slice(&(v as u32).to_le_bytes());
            5
        }
        _ => {
            out[0] = 0xff;
            out[1..9].copy_from_slice(&v.to_le_bytes());
            9
        }
    }
}

pub struct VarintItemRef<'a> {
    pub len: u64,
    pub data: &'a [u8],
}

pub struct VarintListRef<'a> {
    pub count: u64,
    pub items: Vec<VarintItemRef<'a>>,
}

pub fn parse_varint_list(b: &[u8]) -> Option<(usize, VarintListRef<'_>)> {
    let (mut pos, count) = parse_varint(b)?;
    let cap = (count as usize).min(b.len());
    let mut items = Vec::with_capacity(cap);
    for _ in 0..count {
        let (n, len) = parse_varint(&b[pos..])?;
        pos += n;
        let end = pos.checked_add(len as usize)?;
        if b.len() < end {
            return None;
        }
        items.push(VarintItemRef { len, data: &b[pos..end] });
        pos = end;
    }
    Some((pos, VarintListRef { count, items }))
}

pub fn size_varint_list(v: &VarintListRef<'_>) -> Option<usize> {
    if v.items.len() != v.count as usize {
        return None;
    }
    let mut n = varint_len(v.count);
    for i in &v.items {
        if i.data.len() != i.len as usize {
            return None;
        }
        n += varint_len(i.len) + i.data.len();
    }
    Some(n)
}

pub fn write_varint_list(v: &VarintListRef<'_>, out: &mut [u8]) {
    let mut pos = write_varint(v.count, out);
    for i in &v.items {
        pos += write_varint(i.len, &mut out[pos..]);
        let end = pos + i.data.len();
        out[pos..end].copy_from_slice(i.data);
        pos = end;
    }
}

// ---------------------------------------------------------------- bits

/// Mirrors the generated `BitsHeader`.
pub struct HBitsHeader {
    pub version: u8,
    pub ihl: u8,
    pub dscp: u8,
    pub ecn: u8,
}

pub struct HBitsPacket<'a> {
    pub hdr: HBitsHeader,
    pub total_len: u16,
    pub ident: u16,
    pub ttl: u8,
    pub proto: u8,
    pub checksum: u16,
    pub src: &'a [u8],
    pub dst: &'a [u8],
}

pub const BITS_SIZE: usize = 2 + 2 + 2 + 1 + 1 + 2 + 4 + 4;

pub fn parse_bits(b: &[u8]) -> Option<(usize, HBitsPacket<'_>)> {
    if b.len() < BITS_SIZE {
        return None;
    }
    let hdr = u16::from_be_bytes(b[0..2].try_into().unwrap());
    Some((
        BITS_SIZE,
        HBitsPacket {
            hdr: HBitsHeader {
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

pub fn size_bits(v: &HBitsPacket<'_>) -> Option<usize> {
    if v.src.len() != 4 || v.dst.len() != 4 {
        return None;
    }
    // The bit fields must fit their declared widths.
    if v.hdr.version > 0xf || v.hdr.ihl > 0xf || v.hdr.dscp > 0x3f || v.hdr.ecn > 0x3 {
        return None;
    }
    Some(BITS_SIZE)
}

pub fn write_bits(v: &HBitsPacket<'_>, out: &mut [u8]) {
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

// ---------------------------------------------------------- list formats

/// Stands in for both `BoundedItem` and `TailItem`, which are the same shape.
pub struct ItemRef<'a> {
    pub tag: u16,
    pub len: u16,
    pub body: &'a [u8],
}

/// Parses items back to back until `b` is exactly consumed.
fn parse_items(b: &[u8]) -> Option<Vec<ItemRef<'_>>> {
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
        items.push(ItemRef { tag, len, body: &b[pos..end] });
        pos = end;
    }
    Some(items)
}

pub struct BoundedListRef<'a> {
    pub byte_len: u32,
    pub items: Vec<ItemRef<'a>>,
}

pub fn parse_bounded_list(b: &[u8]) -> Option<(usize, BoundedListRef<'_>)> {
    if b.len() < 4 {
        return None;
    }
    let byte_len = u32::from_be_bytes(b[0..4].try_into().unwrap());
    let end = 4usize.checked_add(byte_len as usize)?;
    if b.len() < end {
        return None;
    }
    let items = parse_items(&b[4..end])?;
    Some((end, BoundedListRef { byte_len, items }))
}

pub fn size_bounded_list(v: &BoundedListRef<'_>) -> Option<usize> {
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

pub fn write_bounded_list(v: &BoundedListRef<'_>, out: &mut [u8]) {
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

pub fn parse_tail_list(b: &[u8]) -> Option<(usize, Vec<ItemRef<'_>>)> {
    parse_items(b).map(|items| (b.len(), items))
}

pub fn size_tail_list(items: &[ItemRef<'_>]) -> Option<usize> {
    let mut n = 0usize;
    for i in items {
        if i.body.len() != i.len as usize {
            return None;
        }
        n += 4 + i.body.len();
    }
    Some(n)
}

pub fn write_tail_list(items: &[ItemRef<'_>], out: &mut [u8]) {
    let mut pos = 0;
    for i in items {
        out[pos..pos + 2].copy_from_slice(&i.tag.to_be_bytes());
        out[pos + 2..pos + 4].copy_from_slice(&i.len.to_be_bytes());
        pos += 4;
        let end = pos + i.body.len();
        out[pos..end].copy_from_slice(i.body);
        pos = end;
    }
}
