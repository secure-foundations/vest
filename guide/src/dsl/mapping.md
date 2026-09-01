# Construct-to-Rust mapping

A quick-lookup table from DSL construct to the Rust type it generates.

Names are converted to `UpperCamelCase`: `msg_type` becomes `MsgType`. Alongside
each value type, the compiler emits a zero-sized format type — `MsgTypeFmt` —
that carries the parser, serializer, and proofs. See
[Generated Rust Code](generated-api.md) for the full set of emitted names.

| Vest DSL construct | Generated Rust type |
|---|---|
| `name = u8` (or `u16`, `u24`, `u32`, `u64`) | `type Name = u8` |
| `name = btc_varint` | `type Name = u64` |
| `name = u16 \| {1..0xffff}` | `type Name = u16` |
| `name = enum { A = 1, B = 2, }` | `enum Name { A = 1, B = 2 }` |
| `name = enum { A = 1, B = 2, ... }` | `enum Name { A = 1, B = 2, Unknown(u8) }` |
| `name = enum { A = 0u16, }` | `#[repr(u16)] enum Name { A = 0 }` |
| `name = bits { f1: u4, f2: u4, }` | `struct Name { f1: u8, f2: u8 }` |
| `name = bits { k: my_enum, n: u5 \| {1..31}, }` | `struct Name { k: MyEnum, n: u8 }` |
| `name = [u8; 16]` | `type Name<'i> = &'i [u8]` |
| `name = [u16; 8]` | `type Name = [u16; 8]` |
| `name = Option<inner>` | `Option<Inner>` |
| `name = Vec<inner>` | `Vec<Inner>` |
| `name = Nothing` | `type Name = ()` |
| `name = Never("reason")` | `type Name = Never` |
| `name = Tail` | `type Name = &[u8]` |
| `name(@l: u8) = [u8; @l]` | `type Name = &[u8]` |
| `name(@l: u8) = [u8; @l] >>= Vec<item>` | `type Name = Vec<Item>` |
| `name(@count) = [item; @count]` | `type Name = Vec<Item>` |
| `name = { a: fmt_a, b: fmt_b, }` | `struct Name { a: FmtA, b: FmtB }` |
| `name = { @l: u16, data: [u8; @l], }` | `struct Name { l: u16, data: &[u8] }` |
| `name = { @hdr: header, body: [u8; @hdr.len - 4], }` | `struct Name { hdr: Header, body: &[u8] }` |
| `name = { a: fmt_a, b: Tail, }` | `struct Name { a: FmtA, b: &[u8] }` |
| `name = { const tag: u8 = 0x01, data: u16, }` | `struct Name { tag: u8, data: u16 }` |
| `name(@t: my_type) = choose(@t) { A => fmt_a, _ => fmt_c, }` | `enum Name { A(FmtA), Default(FmtC) }` |
| `name = choose { V1(u8 \| 0..10), V2(u8 \| 11..), }` | `enum Name { V1(u8), V2(u8) }` |
| `name = wrap(u8 = 0x01, inner, u8 = 0xFF)` | same as `inner` |
