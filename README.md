[![CI](https://github.com/secure-foundations/vest/actions/workflows/ci.yml/badge.svg)](https://github.com/secure-foundations/vest/actions/workflows/ci.yml)
[![Documentation](https://img.shields.io/badge/docs-vest__lib-blue)](https://secure-foundations.github.io/vest/vest_lib/)
[![Crates.io - vest](https://img.shields.io/crates/v/vest?label=vest)](https://crates.io/crates/vest)
[![Crates.io - vest_lib](https://img.shields.io/crates/v/vest_lib?label=vest_lib)](https://crates.io/crates/vest_lib)

# Vest

## Overview

Vest is a research project aiming for high-assurance and performant parsing and serialization of _binary data formats_ in [Verus](https://github.com/verus-lang/verus). It features a library of **formally verified** binary parsers, serializers, and their combinators, as well as a domain-specific language (DSL) for expressing binary formats described in external specifications, or used internally in applications. 

Parsers and serializers produced by Vest are guaranteed to satisfy:

- **Memory and arithmetic safety**: 
  - Vest parsers and serializers are implemented in *safe* Rust, so Rust's ownership and borrowing system ensures that they are immune to use-after-free, double-free, and other memory-safety bugs.
  - Vest parsers and serializers are verified using Verus, with which we prove that they are free of out-of-bounds accesses, integer overflows/underflows, and other arithmetic bugs.
- **Termination and panic-freedom**: Vest parsers and serializers are guaranteed to terminate and never panic on any input.
- **Efficiency and functional correctness**: Vest parsers and serializers read/modify *existing* buffers without unnecessary copying or allocation, and are verified to behave exactly as defined by their high-level functional specifications.

For higher assurance, Vest's functional parser and serializer specifications are proven to satisfy the following correctness and security properties, which are crucial for preventing parser malleability and format confusion attacks:

- **Parser soundness**: If the parser successfully parses an input, then the output is guaranteed to be a valid instance of the specified format.
- **Parser completeness**: For every valid instance of the specified format, there exists an input that the parser can successfully parse to produce that instance.
- **Parser non-malleability**: If the parser successfully parses an input, then any *in-place modification* or *truncation* of the input will cause the parser to behave differently (e.g., fail to parse, or produce a different output), ensuring *unique* binary representations.
- **Parser non-extensibility**: If the parser successfully parses an input, then it will produce the same output on any *extension* of the input[^1]. 
- **Serializer non-ambiguity**: No two distinct valid instances of the specified format can be serialized to the same output.
- **Round-trip properties**: For unambiguous and non-malleable formats, the parser and serializer are mutual inverses (i.e., parsing a serialized bytestring should yield the original value, and serializing a parsed value should yield the original bytestring). 

While the above properties are desirable for security-critical protocol/file formats, data formats in the wild can be complex and may not satisfy all of them (e.g., some formats accept non-canonical encodings or provide error tolerance). We aim to provide a flexible framework that gives (non-expert) users the tools to specify and reason about different properties of their formats, and to make informed trade-offs between security and flexibility. Some initial progress towards this goal can be found on [this branch](https://github.com/secure-foundations/vest/tree/vest2.0) (let us know if you're interested in trying it out or contributing to it!).

[^1]: Certain formats (e.g., TLS) do allow for extensions, but only in the *middle* of the format, (which are usually protected by length fields) and hence the format as a whole can still satisfy non-extensibility. We are working on supporting formats that need *tail-extensions* (e.g., *streaming* formats).

## Usage

Vest DSL (implemented in the `vest2` crate) provides a domain-specific language for expressing binary formats in a concise and readable way. The DSL is designed to be close to the syntax of Rust data type declarations, with added expressivity for type refinements, internal field dependencies, length arithmetic, bitfields, mutual recursion, and more—enabling the user to define a wide variety of binary formats found in RFCs and other external specifications. The DSL is type-checked and compiled into verified Rust code backed by the `vest_lib2` combinator library. Though possible, it is recommended to use the DSL rather than composing combinators by hand.

> For worked examples see the `.vest` files and their generated `.rs` counterparts under [`vest2/test/src/`](vest2/test/src/), including real-world case studies for [TLS](vest2/test/src/tls.rs), and [Bitcoin](vest2/test/src/bitcoin.rs).

### `.vest` files

A `.vest` file contains a set of format definitions. The compiler type-checks them and emits, for each definition, a Rust data type, an imperative parser, serializer, and format-compliance checker, plus a combinator-based specification along with the (derived) security proofs. No manual proof work is required.

As a classic example, consider the following `.vest` file defining a [TLV](https://en.wikipedia.org/wiki/Type-length-value) data format:

```vest
msg_type = enum {
  Msg1 = 0x01,
  Msg2 = 0x02,
  Msg3 = 0x03,
}

msg1 = { a: u8, b: u16, c: [u8; 3], data: Tail }
msg2 = { a: u8, b: u16, c: u32 }
msg3 = [u8; 6]

msg = {
  @tag: msg_type,
  @len: u16,
  content: [u8; @len] >>= choose(@tag) {
    Msg1 => msg1,
    Msg2 => msg2,
    Msg3 => msg3,
  },
}
```

Fields prefixed with `@` are *dependent*: they are parsed and bound to a name that can be used in subsequent field expressions. Here `@len` controls how many raw bytes are to be consumed by `content`, and those bytes are then extracted and parsed by the branch selected via `@tag`. The compiler generates roughly the following Rust code (with some details elided):

```rust
// =========================================================================
// Data Types
// =========================================================================
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg<'i> {
    pub tag: MsgType,
    pub len: u16,
    pub content: MsgContent<'i>,
}

#[repr(u8)]
#[derive(Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum MsgType {
    Msg1 = 1,
    Msg2 = 2,
    Msg3 = 3,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum MsgContent<'i> {
    Msg1(Msg1<'i>),
    Msg2(Msg2),
    Msg3(Msg3<'i>),
}

// =========================================================================
// Executable Parser, Serializer, and Prepare APIs
// =========================================================================
pub struct MsgFmt;

impl<'i> Parser<&'i [u8]> for MsgFmt {
    type PT = Msg<'i>;
    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> { ... }
}
impl<'i> Serializer<Msg<'i>> for MsgFmt { 
    fn serialize(&self, v: &Msg<'i>, obuf: &mut Vec<u8>) { ... }
}

impl<'i> Prepare<Msg<'i>> for MsgFmt { 
    fn prepare(&self, v: &Msg<'i>) -> Result<usize, PreSerializeError> { ... }
}


// =========================================================================
// Combinator Specifications & Security Proofs (Verified by Verus)
// =========================================================================

impl MsgFmt {
    pub open spec fn spec_inner() -> Named<Mapped<Bind<MsgTypeFmt, ...>, ...>> {
        Named(
            "msg",
            Mapped {
                inner: Bind(
                    MsgTypeFmt,
                    |tag: MsgTypeSpec| Bind(U16Le, |len| ExactLen(len, MsgContentFmt(tag)))
                ),
                mapper: (
                    |parsed: MsgInner| -> MsgSpec { ... },
                    |value: MsgSpec| -> MsgInner { ... },
                )
            }
        )
    }
}

// Security and correctness properties verified automatically:
impl<'i> SafeParser for MsgFmt { ... }
impl<'i> SoundParser for MsgFmt { ... }
impl<'i> Productive for MsgFmt { ... }
impl<'i> NonTailFmt for MsgFmt { ... }
impl<'i> GoodSerializer for MsgFmt { ... }
impl<'i> SPRoundTrip for MsgFmt { ... }
impl<'i> NonMalleable for MsgFmt { ... }
impl<'i> PSRoundTrip for MsgFmt { ... }
```

- To parse: `let (consumed, msg) = MsgFmt.parse(&input)?;`
- To check format compliance & get serialized length: `let byte_len = MsgFmt.prepare(&msg)?;`
- To serialize: `MsgFmt.serialize(&msg, &mut buf);`

### DSL feature overview

The following table summarises the main DSL constructs and their generated Rust types:

| Vest DSL construct | Generated Rust type | Notes |
|---|---|---|
| `name = u8` (or `u16`, `u24`, `u32`, `u64`) | `type Name = u8` | endianness from file-level `!BIG_ENDIAN` / `!LITTLE_ENDIAN` |
| `name = u16 \| { 1..0xffff }` | `type Name = u16` | integer range / set refinement |
| `name = enum { A = 1, B = 2 }` | `enum Name { A = 1, B = 2 }` | closed enum; unknown tag → parse error |
| `name = enum { A = 1, B = 2, ... }` | `enum Name { A = 1, B = 2, Unknown(u8) }` | open enum; unknown tag → `Unknown(x)` |
| `name = enum { A = 0u16, ... }` | `#[repr(u16)] enum Name { A = 0, ... }` | typed enum (determines wire width) |
| `name = bits { f1: u4, f2: u4 }` | `struct Name { f1: u8, f2: u8 }` | bitfield (must be byte-aligned); the corresponding Rust type for a bitfield is the smallest uint that can hold all the bits (e.g., `u8` for 8 bits, `u16` for 9–16 bits, etc.) |
| `name = bits { k: my_enum, n: u5 \| {1..31}, len: u8 }` | `struct Name { k: MyEnum, n: u8, len: u8 }` | bitfield with (bit-sized) enum and constrained sub-fields |
| `name = [u8; 16]` | `type Name = [u8; 16]` | fixed-length byte array |
| `name = Option<inner>` | `Option<Inner>` | optional field |
| `name = Vec<inner>` | `Vec<Inner>` | repeated items |
| `name = Never("custom error message")` | `type Name = Never` | always-failing branch with a custom error message |
| `name = Nothing` | `type Name = ()` | empty format (always succeeds, consumes/produces nothing) |
| `name(@l: u8) = [u8; @l]` | `type Name = &[u8]` | variable-length byte array |
| `name(@l: u8) = [u8; @l] >>= Vec<item>` | `type Name = Vec<Item>` | variable-length of repeated items |
| `name(@count) = [item; @count]` | `type Name = Vec<Item>` | variable number of repeated items |
| `name = { a: fmt_a, b: fmt_b, ... }` | `struct Name { a: FmtA, b: FmtB, ... }` | struct with sequential fields |
| `name = { @l: u16, data: [u8; @l] }` | `struct Name { l: u16, data: &[u8] }` | struct with internal dependency |
| `name = { @hdr: header, body: [u8; @hdr.len - 4] }` | `struct Name { hdr: Header, body: &[u8] }` | nested field access and length expression |
| `name = { a: fmt_a, b: Tail }` | `struct Name { a: FmtA, b: &[u8] }` | trailing raw bytes |
| `name = { const tag: u8 = 0x01, data: u16 }` | `struct Name { tag: u8, data: u16 }` | constant / magic-byte field |
| `name(@t: my_type) = choose(@t) { A => fmt_a, B => fmt_b, _ => fmt_c }` | `enum Name { A(FmtA), B(FmtB), Default(FmtC) }` | dependent choice (tag-dispatched) |
| `name = choose { Var1(u8 \| 0..10), Var2(u8 \| 11..) }` | `enum Name { Var1(u8), Var2(u8) }` | non-dependent choice (tried in order) |
| `name = wrap(u8 = 0x01, inner, u8 = 0xFF)` | same as `inner` | inner format framed by leading/trailing constants |

#### Syntax highlighting

To enable syntax highlighting for `.vest` files in vim/neovim, copy the [`vest2/vest.vim`](vest2/vest.vim) file to `~/.vim/syntax/` or `~/.config/nvim/syntax/` and add to your init file:

```vim
au BufNewFile,BufRead *.vest setfiletype vest
```

## Development

Make sure you have [Rust](https://www.rust-lang.org/tools/install) and [Verus](https://github.com/verus-lang/verus/blob/main/INSTALL.md) properly installed. Then, clone the repository and run:

- To verify the `vest_lib2` crate only:

```sh
cd vest_lib2
cargo verus verify
```

- To verify _and_ compile the entire `vest_lib2` crate:

```sh
cd vest_lib2
cargo verus build
```

- To verify the generated test formats:

```sh
cd vest2/test
cargo verus verify
```

- To build the Vest DSL compiler:

```sh
cd vest2
cargo build --release
```

- To regenerate a `.rs` file from a `.vest` file (e.g., `tlv.vest`):

```sh
cd vest2/test/src
../target/release/vest2 tlv.vest > tlv.rs
```

## Contributing

Vest is still in the early stages of development, and we welcome contributions from the community to either the core library or the DSL. We are also looking for feedback on the design, usability, and performance of the tool. If you are interested in contributing, please feel free to open an issue or a pull request.

## Publications

[Vest: Verified, Secure, High-Performance Parsing and Serialization for Rust](https://tracycy.com/papers/vest-usenix-security25.pdf). **Yi Cai**, Pratap Singh, Zhengyao Lin, Jay Bosamiya, Joshua Gancher, Milijana Surbatovich, Bryan Parno. In Proceedings of the USENIX Security Symposium, August, 2025.

```bibtex
@inproceedings{vest,
  author    = {Cai, Yi and Singh, Pratap and Lin, Zhengyao and Bosamiya, Jay and Gancher, Joshua and Surbatovich, Milijana and Parno, Bryan},
  booktitle = {Proceedings of the USENIX Security Symposium},
  code      = {https://github.com/secure-foundations/vest},
  month     = {August},
  title     = {{Vest}: Verified, Secure, High-Performance Parsing and Serialization for {Rust}},
  year      = {2025}
}
```
