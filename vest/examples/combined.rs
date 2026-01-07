//! ## Message Format
//!
//! ```vest
//! Packet = {
//!     header: Header,
//!     @payload_len: u16,
//!     payload: [u8; @payload_len] >>= Vec<Record>,
//! }
//!
//! Header = {
//!     const magic: u16 = 0xCAFE,
//!     version: u8,
//!     flags: u8,
//! }
//!
//! Record = {
//!     id: u32,
//!     value: u32,
//! }
//! ```

use vest_lib::properties::*;
use vest_lib::regular::bytes::Variable;
use vest_lib::regular::modifier::{AndThen, Mapped, Mapper};
use vest_lib::regular::repetition::Repeat;
use vest_lib::regular::sequence::{Pair, Preceded};
use vest_lib::regular::tag::Tag;
use vest_lib::regular::uints::{U16Be, U16Le, U32Le, U8};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Record {
    pub id: u32,
    pub value: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Header {
    pub version: u8,
    pub flags: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Packet {
    pub header: Header,
    pub len: u16,
    pub records: Vec<Record>,
}

// Record: (u32, u32) <-> Record
impl From<(u32, u32)> for Record {
    fn from((id, value): (u32, u32)) -> Self {
        Record { id, value }
    }
}

impl From<Record> for (u32, u32) {
    fn from(r: Record) -> Self {
        (r.id, r.value)
    }
}

// Header: (u8, u8) <-> Header
impl From<(u8, u8)> for Header {
    fn from((version, flags): (u8, u8)) -> Self {
        Header { version, flags }
    }
}

impl From<Header> for (u8, u8) {
    fn from(h: Header) -> Self {
        (h.version, h.flags)
    }
}

// Packet: (Header, (u16, Vec<Record>)) <-> Packet
impl From<(Header, (u16, Vec<Record>))> for Packet {
    fn from((header, (len, records)): (Header, (u16, Vec<Record>))) -> Self {
        Packet {
            header,
            len,
            records,
        }
    }
}

impl<'a, 's: 'a> From<&'s Packet> for (Header, (u16, &'a [Record])) {
    fn from(p: &'s Packet) -> Self {
        (p.header, (p.len, &p.records))
    }
}

struct HeaderMapper;

impl Mapper for HeaderMapper {
    type Src<'p> = (u8, u8);
    type Dst<'p> = Header;
    type SrcBorrow<'s> = (u8, u8);
    type DstBorrow<'s> = Header;
    type SrcOwned = (u8, u8);
    type DstOwned = Header;
}

struct RecordMapper;

impl Mapper for RecordMapper {
    type Src<'p> = (u32, u32);
    type Dst<'p> = Record;
    type SrcBorrow<'s> = (u32, u32);
    type DstBorrow<'s> = Record;
    type SrcOwned = (u32, u32);
    type DstOwned = Record;
}

struct PacketMapper;

impl Mapper for PacketMapper {
    type Src<'p> = (Header, (u16, Vec<Record>));
    type Dst<'p> = Packet;
    type SrcBorrow<'s> = (Header, (u16, &'s [Record]));
    type DstBorrow<'s> = &'s Packet;
    type SrcOwned = (Header, (u16, Vec<Record>));
    type DstOwned = Packet;
}

fn record_combinator() -> Mapped<(U32Le, U32Le), RecordMapper> {
    Mapped::new((U32Le, U32Le), RecordMapper)
}

fn header_combinator() -> Mapped<Preceded<Tag<U16Be, u16>, (U8, U8)>, HeaderMapper> {
    let magic = Tag::new(U16Be, 0xCAFEu16);
    Mapped::new(Preceded(magic, (U8, U8)), HeaderMapper)
}

fn payload_combinator(len: u16) -> AndThen<Variable, Repeat<Mapped<(U32Le, U32Le), RecordMapper>>> {
    AndThen(Variable(len as usize), Repeat::new(record_combinator()))
}

type RecordComb = Mapped<(U32Le, U32Le), RecordMapper>;
type PayloadComb = AndThen<Variable, Repeat<RecordComb>>;

type HeaderComb = Mapped<Preceded<Tag<U16Be, u16>, (U8, U8)>, HeaderMapper>;

type PacketCombinator =
    Mapped<(HeaderComb, Pair<U16Le, PayloadComb, fn(u16) -> PayloadComb>), PacketMapper>;

fn packet_combinator() -> PacketCombinator {
    Mapped::new(
        (header_combinator(), Pair::new(U16Le, payload_combinator)),
        PacketMapper,
    )
}

// // type PacketCombinator = (HeaderComb, Pair<U16Le, PayloadComb, fn(u16) -> PayloadComb>);

// fn packet_combinator() -> (HeaderComb, Pair<U16Le, PayloadComb, impl Fn(u16) -> PayloadComb>) {
//     (
//         header_combinator(),
//         // Pair::new(U16Le, payload_combinator),
//         Pair::new(U16Le, |len|
//           AndThen(Variable(len as usize), Repeat::new(record_combinator()))),
//     )
// }

fn example_record() {
    println!("\n=== Record Combinator ===");

    let record_comb = record_combinator();
    let record = Record {
        id: 0x12345678,
        value: 0xDEADBEEF,
    };

    let mut buf = vec![0u8; 16];
    let written = <_ as Combinator<[u8], _>>::serialize(&record_comb, record, &mut buf, 0)
        .expect("serialize");
    println!("  Serialized Record: {:?}", &buf[..written]);
    println!("  Bytes: {:02X?}", &buf[..written]);

    let (consumed, parsed) =
        <_ as Combinator<_, Vec<u8>>>::parse(&record_comb, &buf[..written]).expect("parse");
    println!("  Parsed Record: {:?}", parsed);
    assert_eq!(consumed, 8);
    assert_eq!(parsed.id, 0x12345678);
    assert_eq!(parsed.value, 0xDEADBEEF);
    println!("  Record roundtrip passed!");
}

fn example_header() {
    println!("\n=== Header Combinator ===");

    let header_comb = header_combinator();
    let header = Header {
        version: 1,
        flags: 0x42,
    };

    let mut buf = vec![0u8; 16];
    let written = <_ as Combinator<[u8], _>>::serialize(&header_comb, header, &mut buf, 0)
        .expect("serialize");
    println!("  Serialized Header: {:?}", &buf[..written]);
    println!("  Bytes: {:02X?}", &buf[..written]);
    assert_eq!(&buf[..2], &[0xCA, 0xFE]); // Magic number

    let (consumed, parsed) =
        <_ as Combinator<_, Vec<u8>>>::parse(&header_comb, &buf[..written]).expect("parse");
    println!("  Parsed Header: {:?}", parsed);
    assert_eq!(consumed, 4);
    assert_eq!(parsed.version, 1);
    assert_eq!(parsed.flags, 0x42);
    println!("  Header roundtrip passed!");
}

fn example_payload() {
    println!("\n=== Payload with AndThen (Variable >>= Repeat) ===");

    // Create some records
    let records: [Record; 3] = [
        Record { id: 1, value: 100 },
        Record { id: 2, value: 200 },
        Record { id: 3, value: 300 },
    ];
    let records_slice: &[Record] = &records;

    // Each record is 8 bytes (2 x u32le), so 3 records = 24 bytes
    let payload_len: u16 = 24;

    let payload_comb = payload_combinator(payload_len);

    let mut buf = vec![0u8; 32];
    let written = <_ as Combinator<[u8], _>>::serialize(&payload_comb, records_slice, &mut buf, 0)
        .expect("serialize");
    println!("  Serialized Payload ({} records, {} bytes):", 3, written);
    println!("  Bytes: {:02X?}", &buf[..written]);

    let (consumed, parsed) =
        <_ as Combinator<_, Vec<u8>>>::parse(&payload_comb, &buf[..written]).expect("parse");
    println!("  Parsed {} records:", parsed.len());
    for (i, r) in parsed.iter().enumerate() {
        println!("    Record {}: id={}, value={}", i, r.id, r.value);
    }
    assert_eq!(consumed, 24);
    assert_eq!(parsed.len(), 3);
    assert_eq!(parsed[0], Record { id: 1, value: 100 });
    assert_eq!(parsed[1], Record { id: 2, value: 200 });
    assert_eq!(parsed[2], Record { id: 3, value: 300 });
    println!("  Payload roundtrip passed!");
}

fn example_full_packet() {
    println!("\n=== Full Packet (Header + Dependent Pair + AndThen + Repeat) ===");
    println!("  Format: Preceded(magic, (version, flags)), @len:u16, [u8; @len] >>= Vec<Record>");

    // Use the packet_combinator function
    let pkt_comb = packet_combinator();

    // Create test data
    let header = Header {
        version: 2,
        flags: 0xFF,
    };
    let records: [Record; 2] = [
        Record {
            id: 42,
            value: 1000,
        },
        Record {
            id: 99,
            value: 2000,
        },
    ];
    let records_slice: &[Record] = &records;

    // Payload length: 2 records * 8 bytes = 16 bytes
    let payload_len: u16 = 16;

    let value = Packet {
        header,
        len: payload_len,
        records: records_slice.to_vec(),
    };

    let mut buf = vec![0u8; 64];
    let written =
        <_ as Combinator<[u8], _>>::serialize(&pkt_comb, &value, &mut buf, 0).expect("serialize");

    println!("  Serialized Packet ({} bytes):", written);
    println!("  Full bytes: {:02X?}", &buf[..written]);
    println!("  Breakdown:");
    println!("    Magic:      {:02X?} (0xCAFE)", &buf[0..2]);
    println!("    Version:    {:02X?} ({})", &buf[2..3], buf[2]);
    println!("    Flags:      {:02X?} (0x{:02X})", &buf[3..4], buf[3]);
    println!(
        "    PayloadLen: {:02X?} ({} bytes)",
        &buf[4..6],
        u16::from_le_bytes([buf[4], buf[5]])
    );
    println!("    Payload:    {:02X?}", &buf[6..written]);

    let (consumed, parsed_packet) =
        <_ as Combinator<_, Vec<u8>>>::parse(&pkt_comb, &buf[..written]).expect("parse");

    println!("\n  Parsed Packet:");
    println!(
        "    Header: version={}, flags=0x{:02X}",
        parsed_packet.header.version, parsed_packet.header.flags
    );
    println!("    Payload length: {} bytes", parsed_packet.len);
    println!("    Records ({}):", parsed_packet.records.len());
    for (i, r) in parsed_packet.records.iter().enumerate() {
        println!("      [{}] id={}, value={}", i, r.id, r.value);
    }

    assert_eq!(consumed, written);
    assert_eq!(parsed_packet.header.version, 2);
    assert_eq!(parsed_packet.header.flags, 0xFF);
    assert_eq!(parsed_packet.len, 16);
    assert_eq!(parsed_packet.records.len(), 2);
    assert_eq!(
        parsed_packet.records[0],
        Record {
            id: 42,
            value: 1000
        }
    );
    assert_eq!(
        parsed_packet.records[1],
        Record {
            id: 99,
            value: 2000
        }
    );

    println!("\n  Full packet roundtrip passed!");
}

fn example_packet_generation() {
    println!("\n=== Packet Generation Example ===");

    let pkt_comb = packet_combinator();

    let mut gen_st = GenSt::new(12345); //
    let (generated_bytes, generated_packet) = <_ as Combinator<[u8], Vec<u8>>>::generate(&pkt_comb, &mut gen_st)
        .expect("generate");

    println!("  Generated Packet ({} bytes):", generated_bytes);
    println!(
        "    Header: version={}, flags=0x{:02X}",
        generated_packet.header.version, generated_packet.header.flags
    );
    println!("    Payload length: {} bytes", generated_packet.len);
    println!("    Records ({}):", generated_packet.records.len());
    for (i, r) in generated_packet.records.iter().enumerate() {
        println!("      [{}] id={}, value={}", i, r.id, r.value);
    }

    println!("  Packet generation completed!");
}

fn main() {
    example_record();
    example_header();
    example_payload();
    example_full_packet();
    example_packet_generation();
}
