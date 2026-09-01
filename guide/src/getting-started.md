# Getting started

This tutorial shows how to install Vest, define a simple tag-length-value (TLV) format in the DSL, compile it to Rust, parse a message in that format, and serialize a value according to the format.

## Install

Prerequisites: a stable Rust toolchain with `cargo` and `rustc` on your `PATH`.

```console
cargo install vest
```

That puts the `vest` compiler on your `PATH`. In the crate that will hold the
generated code, add the following dependencies to `Cargo.toml`:

```console
cargo add vest_lib
cargo add vstd@=0.0.0-2026-08-23-0033 --no-default-features
```

which gives you:

```toml
[dependencies]
vest_lib = "0.2"
vstd = { version = "=0.0.0-2026-08-23-0033", default-features = false }
```

Generated modules refer to `vstd` directly, so it has to be a direct dependency even when you are only compiling and running the executable Rust. The version has to be exact (we'll try to keep this doc up to date as much as possible): Verus and `vstd` move quickly, and each Vest release tracks one
release of each.

`vest_lib` has three configurations — the default `std`,
`alloc` alone for `no_std` with a heap, and neither for `core`-only. See
[Feature configurations](library/features.md).

## Describe a format

Tag-length-value (TLV) is the shape underneath most network protocols: a tag says what
follows, a length delimits it, and the body is interpreted according to the tag.

Create `msg.vest`:

```vest
msg_type = enum {
  Msg1 = 1,
  Msg2 = 2,
  Msg3 = 3,
}

msg1 = { a: u8, b: u16, c: [u8; 3], data: Tail, }
msg2 = { a: u8, b: u16, c: u32, }
msg3 = { data: [u8; 6], }

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

The syntax is mostly self-explanatory, akin to those of Rust.
There are a few things to notice inside the `msg` definition:

- `@tag` and `@len` are field *dependencies*.
  The `@` prefix lets later fields refer
  to them. They are still ordinary fields of the generated struct, and of course still
  bytes on the wire — `@` only signals that they are used in later format expressions.
- `[u8; @len]` carves out exactly `len` bytes.
- `>>= choose(@tag)` then reparses *that region* with the format chosen by `tag`. Because the
  region is bounded first, a body that tries to read past its length fails
  instead of silently consuming bytes from the next message. We will see what it means for serialization shortly.

Integers are little-endian by default.
Add `!BIG_ENDIAN` at the top of the file to switch to big-endian.

## Generate Rust

```console
$ vest msg.vest -o src/msg.rs
📜 Parsing the vest file...
🔨 Elaborating the AST...
🔍 Type checking...
📝 Generating the verus file...
👏 Done!
```

Without `-o`, the compiler writes next to the input, replacing the extension —
`msg.vest` becomes `msg.rs`. The generated module is a normal Rust file, so you can `mod msg;` it and use it like any other module.

You get one value type per definition, plus a zero-sized format type carrying
the parser, serializer, and proofs:

```rust,ignore
pub enum MsgType { Msg1 = 1, Msg2 = 2, Msg3 = 3 }

pub struct Msg1<'i> { pub a: u8, pub b: u16, pub c: &'i [u8], pub data: &'i [u8] }
pub struct Msg2      { pub a: u8, pub b: u16, pub c: u32 }
pub struct Msg3<'i>  { pub data: &'i [u8] }

pub enum MsgContent<'i> { Msg1(Msg1<'i>), Msg2(Msg2), Msg3(Msg3<'i>) }

pub struct Msg<'i> {
    pub tag: MsgType,
    pub len: u16,
    pub content: MsgContent<'i>,
}

pub struct MsgFmt;   // the format: parser + serializer + proofs

// ... specifications, proofs, and executable APIs
```


## Checking the proofs (highly recommended)

Technically, *you do not need to install Verus to use Vest*, especially if you are working with unverified Rust and just want to parse and serialize things more safely.
However, Vest-generated code comes with specifications and proofs that establish the correctness and security of the parser and serializer.
It is therefore highly recommended to use Verus to automatically check the proofs (rather than trusting the DSL compiler)
to ensure that the generated code indeed satisfies the [desired properties](guarantees.md).

Verus and `vstd` move quickly, and each Vest release tracks one exact Verus
release, recorded in
[`verus-version.txt`](https://github.com/secure-foundations/vest/blob/main/verus-version.txt).
Follow the [Verus installation instructions](https://github.com/verus-lang/verus/blob/main/INSTALL.md)
and match that version, or let the script in the Vest repository install it for you:

```console
git clone https://github.com/secure-foundations/vest.git
./vest/scripts/install-verus.sh
export PATH="$PWD/vest/.verus:$PATH"
```

Then verify *your own crate* — the one holding the generated module:

```console
cd my-project
cargo verus verify
```

Verus checks every specification and proof in `src/msg.rs`, so a clean run
means the guarantees hold for your format.


## Parse

```rust,ignore
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};
use crate::msg::*;

let wire: &[u8] = &[
    0x02,                               // tag = Msg2
    0x07, 0x00,                         // len = 7
    0xAA,                               // a
    0xBB, 0xCC,                         // b
    0xDD, 0xEE, 0xFF, 0x11,             // c
];

let (consumed, msg) = MsgFmt.parse(&wire).unwrap();
assert_eq!(consumed, 10);
assert_eq!(msg.tag, MsgType::Msg2);
assert_eq!(msg.len, 7);
assert!(matches!(msg.content, MsgContent::Msg2(_)));
```

`parse` returns how many bytes it consumed, so a caller reading a stream knows
where the next message begins (it does not mandate that the input slice end exactly at the message boundary). The `msg` value in the example copies and re-interprets the wire bytes because `msg2` only contains fixed-size integers (where "zero-copy" pointers to the input buffer would be even less efficient).
For larger payloads, Vest uses borrowed slices to avoid unnecessary copies/allocations.

## Serialize (and beyond)

Serializing in Vest is two steps.
The standard way is to call `prepare` first, which dynamically checks that the value is valid (we will see what that means) and returns the exact wire length of the serialized representation.
Then you allocate a buffer of that length and call `serialize` to write into it. This two-step process allows Vest to serialize without failing, nor allocating memory during serialization.

Using the `msg` value from the parse example:

```rust,ignore
let len = MsgFmt.prepare(&msg).unwrap();
let mut output = vec![0u8; len];
MsgFmt.serialize(&msg, &mut output);
assert_eq!(output.as_slice(), wire);
```

Now build a new `msg` from scratch:

```rust,ignore
let msg = Msg {
    tag: MsgType::Msg2,
    len: 7, // u8 + u16 + u32 = 1 + 2 + 4 = 7
    content: MsgContent::Msg2(Msg2 { a: 0xAA, b: 0xBBCC, c: 0xDDEEFF11 }),
};

let len = MsgFmt.prepare(&msg).unwrap();   // 10
```

A wrong `len` is rejected by `prepare`:

```rust,ignore
let bad = Msg {
    tag: MsgType::Msg2,
    len: 99, // wrong length for the content
    content: MsgContent::Msg2(Msg2 { a: 0xAA, b: 0xBBCC, c: 0xDDEEFF11 }),
};

assert!(MsgFmt.prepare(&bad).is_err());
```

The error names the problem:

```text
PreSerializeError { kind: NotCompliant(LengthInconsistent), .. }
```

This is the field dependency being enforced in the *other* direction.
Unlike for parsing, where `@len` determines how many bytes to read subsequently,
a dependency
like `@len` is
a constraint the value must satisfy before serialization, and `prepare` is where that is checked.

<!--Finally, for verified code, you can statically prove that a value is valid and its length is less than some bound, and then call `length` and `serialize` without dynamic validity checks nor integer overflow checks. -->

## What was proven

The generated module carries proofs that, among other things, parsing/serializing is memory and arithmetically safe, panic-free, and
terminating; and that a successful parse reconstructs the original serialized value and consumes exactly as many bytes as the value would serialize to.
See [What Vest proves](guarantees.md) for a complete list of properties and the interfaces that carry them.


## Where next

- [Language reference](dsl/reference.md) — every format construct, and the current limitations.
- [Generated Rust Code](dsl/generated-api.md) — the full shape of what comes out of the compiler.
- [Troubleshooting](troubleshooting.md) — what the common errors mean.
- [ASN.1 frontend](asn1/index.md) — generate DER or BER from an ASN.1 module instead of writing a `.vest` file.
