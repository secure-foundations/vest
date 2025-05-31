# Vest

## Overview

Vest is a research project aiming for high-assurance and performant parsing and serialization of _binary data formats_ in [Verus](https://github.com/verus-lang/verus). It features a library of **formally verified** binary parsers, serializers, and their combinators, as well as a domain-specific language (DSL) for expressing binary formats described in RFCs or other specifications.

## Background

**Parsing and serialization of binary data**

In the context of binary formats, parsing refers to the process of interpreting raw byte sequences as structured data, while serialization refers to the reverse process of encoding structured data as raw byte sequences. Binary formats are essential in domains like network protocols, file systems, and embedded systems, where data is often transmitted or stored in a compact binary form.

**Formally verified parsing and serialization**

Binary formats are notoriously difficult to parse and serialize correctly, due to the complexity of the formats and the potential for errors in the (highly-optimized) implementation. Vest aims to address this problem by _formally verifying_ the correctness and security of the efficient parsing and serialization code using the Rust type system and [Verus](https://github.com/verus-lang/verus), a deductive verification tool for Rust.

We leverage Rust's ownership, borrowing, and lifetime system to _safely_ implement "zero-copy" parsing and "in-place" serialization of binary formats, which means that we can parse and serialize binary data without any unnecessary copying or allocation. We don't use `unsafe` so the Rust type system provides us with strong guarantees about the memory safety of the code. We use Verus to verify the more nuanced properties of the code, such as the top-level round-trip properties of the parsing and serialization functions.

- For every binary sequence `b`, if `parse(b)` succeeds, producing a result `(n, m)`, then `serialize(m)` should reproduce the original input `b`, truncated to `n` bytes.
- For every structured data `m`, if `serialize(m)` produces a binary sequence `b`, then `parse(b)` should successfully consuming the entire input `b` and produce the original structured data `m`.

These round-trip properties ensure that the parsing and serialization functions are mutual inverses and hence immune to parser malleability attacks ([EverParse](https://www.microsoft.com/en-us/research/publication/everparse/)) and format confusion attacks ([Comparse](https://dl.acm.org/doi/10.1145/3576915.3623201)).

**Parser and serializer combinators**

It's certainly possible to implement and verify parsers and serializers for single protocol formats or file formats manually, but this approach is tedious, and not reusable. Binary formats often share common patterns, such as fixed-size fields, variable-size fields, a sequence of fields, a tagged union of fields, repeated fields, etc.

Leveraging the power of Rust's traits and generics,
Vest provides a set of combinators with unified interface (for both parsing and serializing) that can be used to build complex parsers and serializers from simple ones, where the formal properties of the combinators are verified once and for all.

## Usage

Vest DSL (implemented separately in the `vest-dsl` crate) provides a domain-specific language (DSL) for expressing binary formats in a concise and readable way. The DSL is designed to be close to the syntax of Rust data type declarations, with added expressivity like type refinements, internal dependencies within formats, and external dependencies among different formats, enabling the user to define a variety of binary formats found in RFCs or other external specifications. The DSL is type checked and translated into a set of combinators defined and verified in the `vest` crate. It's recommended to use the Vest DSL to define binary formats to avoid the boilerplate of manually constructing combinators, but it's also possible to use the combinators directly.

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
struct TlvMsg {
    t: MsgType,
    l: u16,
    v: TlvMsgV,
}

type MsgType = u8;

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

Once the generated code is type-checked by Rust and verified by Verus, the user can confidently use them in their applications as "one-liners":

```rust
fn parse_tlv_msg(i: &[u8]) -> (o: Result<(usize, TlvMsg), Error>) {
    tlv_msg().parse(i)
}
fn serialize_tlv_msg(v: &TlvMsg, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, Error>) {
    tlv_msg().serialize(v, data, pos)
}
```

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

### Directly using combinators

In case the user wants more control over the parsing and serialization process, they can use the combinators directly.

#### Example: Parsing and serializing a pair of bytes

```rust
use vest::regular::bytes::*;

let pair_of_bytes = (Fixed::<1>, Fixed::<2>);

let input = &[0x10; 10];
let (consumed, (a, b)) = pair_of_bytes.parse(input)?;

let mut output = vec![0x00; 40];
let written = pair_of_bytes.serialize((&a, &b), &mut output, 0)?;

proof { pair_of_bytes@.theorem_parse_serialize_roundtrip(input@); }
assert(written == consumed);
assert(&output[..written]@, &input[..written]@);
```

#### Example: Constructing a new combinator

```rust
use vest::regular::uints::U8;
use vest::regular::modifier::{Refined, Pred};

pub struct EvenU8;
impl Pred for EvenU8 {
    type Input = u8;
    fn apply(&self, i: &Self::Input) -> bool {
        *i % 2 == 0
    }
}

let even_u8 = Refined { inner: U8, predicate: EvenU8 };

let mut output = vec![0x00; 40];
let ten = 10u8;
let written = even_u8.serialize(&ten, &mut output, 0)?;

let (consumed, parsed) = even_u8.parse(output.as_slice())?;

proof { even_u8@.theorem_serialize_parse_roundtrip(ten@); }
assert(written == consumed);
assert(parsed@, ten@);
```

## Development

Make sure you have [Rust](https://www.rust-lang.org/tools/install) and [Verus](https://github.com/verus-lang/verus/blob/main/INSTALL.md) properly installed. Then, clone the repository and run:

- To verify and compile the entire `vest` crate:

```sh
cd vest
make
```

- To verify the examples:

```sh
cd vest-examples
make
```

- To use the Vest DSL:

```sh
cd vest-dsl
cargo run path/to/your/file.vest
```

- Or you can build the `vest-dsl` crate and use the binary directly:

```sh
cd vest-dsl
cargo build --release
./target/release/vest-dsl --help
Usage: vest-dsl [OPTIONS] <VEST_FILE>

Arguments:
  <VEST_FILE>  Name or directory of the vest file

Options:
  -o, --output <OUTPUT>  Name of the output verus file
  -h, --help             Print help
  -V, --version          Print version
```

## Contributing

Vest is still in the early stages of development, and we welcome contributions from the community to either the core library or the DSL. We are also looking for feedback on the design, usability, and performance of the tool. If you are interested in contributing, please feel free to open an issue or a pull request.
