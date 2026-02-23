[![CI](https://github.com/secure-foundations/vest/actions/workflows/ci.yml/badge.svg)](https://github.com/secure-foundations/vest/actions/workflows/ci.yml)
[![Documentation](https://img.shields.io/badge/docs-vest__lib-blue)](https://secure-foundations.github.io/vest/vest_lib/)
[![Crates.io - vest](https://img.shields.io/crates/v/vest?label=vest)](https://crates.io/crates/vest)
[![Crates.io - vest_lib](https://img.shields.io/crates/v/vest_lib?label=vest_lib)](https://crates.io/crates/vest_lib)

# Vest

## Overview

Vest is a research project aiming for high-assurance and performant parsing and serialization of _binary data formats_ in [Verus](https://github.com/verus-lang/verus). It features a library of **formally verified** binary parsers, serializers, and their combinators, as well as a domain-specific language (DSL) for expressing binary formats described in external specifications, or used internally in applications. 

Parsers and serializers produced by Vest are guaranteed to satisfy:

- **Memory and arithmetic safety**: 
  - Vest parsers and serializers are implemented in *safe* Rust, so the Rust's ownership and borrowing system ensures that they are immune to use-after-free, double-free, among other memory safety bugs.
  - Vest parsers and serializers are verified using Verus, with which we prove that they are free of out-of-bounds accesses, integer overflows/underflows, and other arithmetic bugs.
- **Termination and panic-freedom**: Vest parsers and serializers are guaranteed to terminate and never panic on any input.
- **Efficiency and functional correctness**: Vest parsers and serializers read/modify *existing* buffers without unnecessary copying or allocation, and are verified to behave exactly as defined by their high-level functional specifications.

For higher assurance, Vest's functional parser and serializer specifications are proven to satisfy the following correctness and security properties, which are crucial for preventing parser malleability and format confusion attacks:

- **Parser soundness**: If the parser successfully parses an input, then the output is guaranteed to be a valid instance of the specified format.
- **Parser completeness (surjectivity)**: For every valid instance of the specified format, there exists an input that the parser can successfully parse to produce that instance.
- **Parser non-malleability (injectivity)**: If the parser successfully parses an input, then any modification to the input will cause the parser to behave differently (e.g., fail to parse, or produce a different output), preventing parser malleability attacks.
- **Serializer injectivity**: No two different valid instances of the specified format can be serialized to the same output.
- **Round-trip properties**: For unambiguous and non-malleable formats, the parser and serializer are mutual inverses (i.e., parsing a serialized bytestring should yield the original value, and serializing a parsed value should yield the original bytestring). 

> While the above properties are desirable for security-critical protocol/file formats, data formats in the wild can be complex and may not satisfy all of them (e.g., formats that accept non-canonical encodings, or even "error-tolerant"). We aim to provide a flexible framework that provides (non-expert) users with the tools to specify and reason about different properties of their formats, and to make informed trade-offs between security and flexibility. Some initial progress towards this goal can be found at [this branch](https://github.com/secure-foundations/vest/tree/vest2.0) (let us know if you're interested in trying it out or contributing to it!).

## Usage

Vest DSL (implemented separately in the `vest-dsl` crate) provides a domain-specific language (DSL) for expressing binary formats in a concise and readable way. The DSL is designed to be close to the syntax of Rust data type declarations, with added expressivity like type refinements, internal dependencies within formats, and external dependencies among different formats, enabling the user to define a variety of binary formats found in RFCs or other external specifications. The DSL is type checked and translated into a set of combinators defined and verified in the `vest` crate. It's recommended to use the Vest DSL to define binary formats to avoid the boilerplate of manually constructing combinators, but it's also possible to use the combinators directly.

> While we are actively working on a more complete documentation of Vest DSL, you may find [vest-examples](vest-examples/README.md) for an overview of how to construct various binary formats using the DSL or directly using combinators.

### `.vest` files

A `.vest` file contains a set of format definitions, each of which defines a binary format using the Vest DSL and will be translated into a corresponding Rust data type and a pair of parsing and serialization functions. As a classic example, consider the following `.vest` file defining a [TLV](https://en.wikipedia.org/wiki/Type-length-value) data format:

```vest
// TLV format
tlv_msg = {
  @t: msg_type,
  @l: u16,
  v: [u8; @l] >>= choose (@t) {
    MsgType1 => type1_msg,
    MsgType2 => type2_msg,
    MsgType3 => type3_msg,
  },
}

msg_type = enum {
  MsgType1 = 0x01,
  MsgType2 = 0x02,
  MsgType3 = 0x03,
}

type1_msg = ...
type2_msg = ...
type3_msg = ...
```

The `.vest` file defines a `tlv_msg` format, which consists of a message type `t`, a length `l`, and a value `v` (the `@` prefix means that those are dependent fields and can be referenced later). The value `v` is a byte sequence of length `l`, and the message type `t` determines how the value should be interpreted. `msg_type` defines an enumeration of message types, and the `choose` syntax is used to select the appropriate message format based on the message type `t`. The `type1_msg`, `type2_msg`, and `type3_msg` formats define the specific message formats for each sub-message type. Roughly, this `.vest` file would correspond to the following Rust data types and functions:

```rust
fn parse_tlv_msg(i: &[u8]) -> Result<(usize, TlvMsg), Error> {
    tlv_msg().parse(i)
}

fn serialize_tlv_msg(v: &TlvMsg, data: &mut Vec<u8>, pos: usize) -> Result<usize, Error> {
    tlv_msg().serialize(v, data, pos)
}

fn tlv_msg_len(v: &TlvMsg) -> usize {
    tlv_msg().length(v)
}

struct TlvMsg {
    t: MsgType,
    l: u16,
    v: TlvMsgV,
}

enum MsgType {
  MsgType1 = 0x01,
  MsgType2 = 0x02,
  MsgType3 = 0x03,
}

enum TlvMsgV {
    MsgType1(Type1Msg),
    MsgType2(Type2Msg),
    MsgType3(Type3Msg),
}

struct Type1Msg { ... }
struct Type2Msg { ... }
struct Type3Msg { ... }

fn tlv_msg() -> TlvMsgCombinator {
    Mapped { inner: Pair((U8, U16), |(t, l)| tlv_msg_v(t, l)), mapper: TlvMsgMapper }
}

fn tlv_msg_v(t: MsgType, l: u16) -> TlvMsgVCombinator {
    AndThen(
        Bytes(l as usize),
        Mapped {
            inner: Choice(
                Choice(
                    Cond { lhs: t, rhs: 1, inner: type1_msg() },
                    Cond { lhs: t, rhs: 2, inner: type2_msg() },
                ),
                Cond { lhs: t, rhs: 3, inner: type3_msg() },
            ),
            mapper: TlvMsgVMapper,
        },
    )
}

fn type1_msg() -> Type1MsgCombinator { ... }
fn type2_msg() -> Type2MsgCombinator { ... }
fn type3_msg() -> Type3MsgCombinator { ... }
//
// specification and proof code (no manual verification needed)
//
```

Specifically, the `tlv_msg` function constructs a combinator for parsing and serializing the `tlv_msg` format, which is a mapped combinator that maps between the structural representation of the format (a pair of `t` and `l`, followed by the value `v`) and the nominal Rust data type (`struct TlvMsg`). The `tlv_msg_v` function constructs a combinator for parsing and serializing the value `v`, which is an `AndThen` combinator that first takes a byte sequence of length `l`, and then uses nested `Choice` combinators to select the appropriate sub-message format based on the message type `t`. The `type1_msg`, `type2_msg`, and `type3_msg` functions construct combinators for parsing and serializing the specific message formats.

- To parse a `tlv_msg` from a byte slice `i`, simply do `let (consumed, msg) = parse_tlv_msg(i)?;`.
- To serialize a `tlv_msg` `msg`, first calculate the required length using `let len = tlv_msg_len(&msg);`, then create a mutable byte buffer of that length, and finally call `let written = serialize_tlv_msg(&msg, &mut buffer, 0)?;`.

The following table briefly summarizes the correspondence between the Vest DSL format definitions and the generated Rust data types and combinators:

| Vest DSL                                                               | Rust Data Type                             | Rust Combinator                                                                    |
| ---------------------------------------------------------------------- | ------------------------------------------ | ---------------------------------------------------------------------------------- |
| `msg_name = u8` (or `u16`, `u24`, etc.)                                | `type MsgName = u8`                        | `U8`                                                                               |
| `msg_name = u8 \| {32}`                                                | `type MsgName = u8`                        | `Refined { inner: U8, predicate: U8Is32 }`                                         |
| `msg_name = enum { A = 1, B = 2, ... }`                                | `type MsgName = u8`                        | `U8`                                                                               |
| `msg_name = enum { A = 3100, B = 3101, ... }`                          | `type MsgName = u16`                       | `U16`                                                                              |
| `msg_name = [u8; 16]`                                                  | `type MsgName = &[u8]`                     | `bytes::Fixed::<16>`                                                               |
| `msg_name(@l) = [u8; @l]`                                              | `type MsgName = &[u8]`                     | `bytes::Variable(l as usize)`                                                      |
| `msg_name(@l) = [msg_a; @l]`                                           | `type MsgName = Vec<MsgA>`                 | `RepeatN(msg_a(), l as usize)`                                                     |
| `msg_name(@l) = [u8; @l] >>= Vec<msg_a>`                               | `type MsgName = Vec<MsgA>`                 | `bytes::Variable(l as usize).and_then(Repeat(msg_a()))`                            |
| `msg_name = { a: msg_a, b: msg_b, ... }`                               | `struct MsgName { a: MsaA, b: MsaB, ... }` | `Mapped { inner: ((msg_a(), msg_b(), ...), ...), mapper: MsgNameMapper }`          |
| `msg_name = { a: msg_a, b: Tail }`                                     | `struct MsgName { a: MsaA, b: &[u8] }`     | `Mapped { inner: (msg_a(),Tail), mapper: MsgNameMapper }`                          |
| `msg_name = { @l: u16, b: [u8; @l] }`                                  | `struct MsgName { l: u16, b: &[u8] }`      | `Mapped { inner: Pair(U16, \|l: u16\| Bytes(l as usize)), mapper: MsgNameMapper }` |
| `msg_name(@t: msg_type) = choose (@t) { A => msg_a, B => msg_b, ... }` | `enum MsgName { A(MsgA), B(MsgB), ... }`   | `Mapped { inner: Choice(Choice(msg_a(), msg_b()), ...), mapper: MsgNameMapper }`   |

The `xxxMapper`s are automatically generated by the Vest DSL compiler and are used to convert between the structural representation of the format (nested products or sums) and the nominal Rust data types (`struct`s and `enum`s).

#### Syntax highlighting

To enable syntax highlighting for `.vest` files in vim/neovim, paste the [vest.vim](vest-dsl/vest.vim) file in your `~/.vim/syntax/` or `~/.config/nvim/syntax/` directory and add the following line to your `~/.vimrc` or `~/.config/nvim/init.vim` file:

```vim
au BufNewFile,BufRead *.vest setfiletype vest
```

## Development

Make sure you have [Rust](https://www.rust-lang.org/tools/install) and [Verus](https://github.com/verus-lang/verus/blob/main/INSTALL.md) properly installed. Then, clone the repository and run:

- To verify the `vest_lib` crate only:

```sh
cd vest
cargo verus verify
```

- To verify _and_ compile the entire `vest_lib` crate:

```sh
cd vest
cargo verus build
```

- To verify the examples:

```sh
cd vest-examples
cargo verus verify
```

- To build the Vest DSL:

```sh
cd vest-dsl
cargo build --release
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
