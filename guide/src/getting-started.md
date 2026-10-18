# Getting started

In this tutorial, we'll use Vest to build a parser and a serializer for
a small binary message format. Along the way, we'll see the typical workflow for using Vest:

- describing a binary format in the Vest DSL,
- compiling the DSL format to Rust,
- parsing raw bytes into Rust values,
- serializing Rust values into bytes,
- and (for verified clients) checking and using the proofs that come with the generated code.

We assume the reader has some basic familiarity with Rust, but no prior knowledge of
[Verus](https://github.com/verus-lang/verus), the program verifier used by Vest.

## What we're building

Many data formats encode messages as [*tag-length-value*](https://en.wikipedia.org/wiki/Type–length–value)
(TLV) structures. In a TLV,
a tag says what kind of message follows, a length says how many bytes it takes,
and the rest of the message is interpreted according to the tag.
Our format follows this pattern: it's a tiny protocol that a sensor might use to
report to a server. Every message starts with a fixed three-byte header followed by a variable-length body:

```text
 byte 0     bytes 1-2          the next `len` bytes
+--------+------------------+--------------------------+
|  tag   |       len        |         content          |
+--------+------------------+--------------------------+
  1 byte   16-bit integer,     interpreted according
           little-endian            to the tag
```

There are three kinds of messages:

| Tag | Message | Content |
| --- | --- | --- |
| 1 | Hello | `version` (1 byte) and `mac` (the sensor's 6-byte MAC address) |
| 2 | Reading | `sensor` (1 byte), `value` (16-bit integer), and `timestamp` (32-bit Unix time) |
| 3 | Log | `level` (1 byte) and `text` (every remaining content byte) |

Note that there are two implicit dependencies/constraints concealed in the above informal format description.
First, the content's structure depends on the tag: a `Hello` message has a different layout than a `Reading` or a `Log`.
Second, the content's byte length must agree with `len` exactly: a `Reading`, for example, always has `len = 7` (1 + 2 + 4 bytes).

A hand-written parser for this seemingly simple format can easily go wrong.
It might forget to check `len` against the input it actually received, let a message body
read past its declared length, or silently accept a tag it doesn't know. A hand-written
serializer can also easily write a `len` that doesn't match the content.
We'll see how Vest takes care of each of these for us.

## Setting up

### Install the compiler

You'll need a stable Rust toolchain with `cargo` and `rustc` on your `PATH`.
Install the Vest DSL compiler from crates.io:

```console
cargo install vest
```

This puts `vest` on your `PATH`. You can run `vest --version` to check that it worked.

### Create a project

Next, let's create a new Rust project and add Verus and Vest as dependencies:

```console
cargo new msg-demo
cd msg-demo
cargo add vest_lib
cargo add vstd@=0.0.0-2026-10-04-0306 --no-default-features
```

Your `Cargo.toml` should now contain something like this:

```toml
[dependencies]
vest_lib = "0.2"
vstd = { version = "=0.0.0-2026-10-04-0306", default-features = false }
```

> **`vest_lib` and `vstd`:** `vest_lib` is Vest's combinator library underlying the generated code.
> It provides the parser and serializer building blocks, together with their specifications and proofs.
> `vstd` is the Verus standard library that `vest_lib` depends on.

> To avoid subtle version mismatch issues, it's advised to use the exact version shown above: Verus and `vstd` move quickly,
> and each Vest release tracks one release of Verus. We'll keep this page up to date as new versions come out.

`vest_lib` supports `no_std` (`core`-only and `alloc`), so you can use it in embedded or kernel code.
See [Feature configurations](library/features.md).

## Writing your first format

Vest formats live in `.vest` files. We'll write `msg.vest` in the project's root
directory, building it one piece at a time.

### The tag: an enum

Let's start with the tag:

```vest
msg_type = enum {
  Hello = 1,
  Reading = 2,
  Log = 3,
}
```

Every format definition has the shape `name = format`. Here, `msg_type` is an *enum*:
a named set of variants, each with a numeric value. The values are the bytes that appear on the wire.
Vest picks the smallest unsigned integer type that holds every value, so this tag takes exactly
one byte. To force a specific integer type, use integer literals with type suffixes like `1u8` or `2u16` for the variants.

This enum is *closed*: the generated parser rejects every other byte value, such
as 4, as an invalid tag. If your protocol
needs to keep unknown tags around instead, add `...` after the variants to make
the enum [open](dsl/enums.md#open-enums).

### The content: three structs

Now let's describe the three kinds of content from the table above:

```vest
hello = {
    version: u8,
    mac: [u8; 6],
}
reading = {
    sensor: u8,
    value: u16,
    timestamp: u32,
}
log = {
    level: u8,
    text: Tail,
}
```

Each definition describes a *struct*: named fields laid out *back to back* on
the wire, with no padding in between. We've used three kinds of building blocks:

- `u8`, `u16`, and `u32` are unsigned integers of 1, 2, and 4 bytes.
- `[u8; 6]` is exactly six raw bytes: here, a MAC address.
- `Tail` means "whatever is left." In `log`, the `text` field takes all the
  bytes that remain after `level`.

### The message: putting it together

Finally, the message itself:

```vest,ignore
msg = {
  @tag: msg_type,
  @len: u16,
  content: [u8; @len] >>= choose(@tag) {
    Hello => hello,
    Reading => reading,
    Log => log,
  },
}
```

Let's decode it line by line:

- `@tag: msg_type` specifies the tag with the enum format we defined earlier. The `@` marks
  `tag` as a *dependency*, which means that later fields can refer to its value
  as `@tag`. It's otherwise the same as an ordinary field: it's on the wire, and it will be
  part of the Rust value type that gets generated.
- `@len: u16` specifies the 16-bit length as an unsigned integer, which is also a dependency.
- `[u8; @len]` carves out exactly `len` bytes of input for the content.
- `>>=`, read as "and then," parses those bytes (and only those bytes) in `[u8; @len]`, with the
  format on its right-hand side. We'll see its role in serialization later.
- `choose(@tag) { ... }` picks that format based on the tag: a `Hello` tag selects the `hello` format, and so on.

The `>>=` operator is important: it "separates" the content from the rest of the input.
The content format only ever sees the
`len` bytes carved out for it, so it can't read past the end of its message.
It also has to use all of them: leftover bytes are a parsing error.

### Byte order

Our protocol spec said that `len` is little-endian. That's Vest's default, so we
don't need to write anything. For a big-endian protocol, put `!BIG_ENDIAN` at
the top of the file; it applies to *every definition* in the file. See
[Byte order](dsl/lexical.md#byte-order) for details.

### The complete file

```vest
msg_type = enum {
  Hello = 1,
  Reading = 2,
  Log = 3,
}

hello = {
    version: u8,
    mac: [u8; 6],
}
reading = {
    sensor: u8,
    value: u16,
    timestamp: u32,
}
log = {
    level: u8,
    text: Tail,
}

msg = {
  @tag: msg_type,
  @len: u16,
  content: [u8; @len] >>= choose(@tag) {
    Hello => hello,
    Reading => reading,
    Log => log,
  },
}
```

## Generating Rust

Now let's compile the format to a Rust module and save it in `src/msg.rs`.

```console
$ vest msg.vest -o src/msg.rs
📜 Parsing the vest file...
🔨 Elaborating the AST...
🔍 Type checking...
📝 Generating the verus file...
👏 Done!
```

The generated module is a normal Rust file. To use it, declare it at the top of
`src/main.rs`:

```rust,ignore
mod msg;
```

> **Tip:** Instead of rerunning the compiler by hand whenever the format
> changes, you can [call it from `build.rs`](dsl/cli.md#generating-from-buildrs)
> to keep the generated code up to date automatically.

### What got generated?

If you open `src/msg.rs`, you'll find that it's quite long (but hopefully still readable!).
That's because it contains specifications and proofs as well as executable code. The parts you'll
interact with are a Rust value type for each definition, plus a *format type* that
does the parsing and serializing:

```rust,ignore
pub enum MsgType { Hello = 1, Reading = 2, Log = 3 }

pub struct Hello<'i> { pub version: u8, pub mac: &'i [u8] }
pub struct Reading   { pub sensor: u8, pub value: u16, pub timestamp: u32 }
pub struct Log<'i>   { pub level: u8, pub text: &'i [u8] }

pub enum MsgContent<'i> { Hello(Hello<'i>), Reading(Reading), Log(Log<'i>) }

pub struct Msg<'i> {
    pub tag: MsgType,
    pub len: u16,
    pub content: MsgContent<'i>,
}

// carries the executable parser, serializer, as well as the specs and proofs for the `msg` format
pub struct MsgFmt;

// ... specifications, proofs, and the implementations of the APIs
```

There's a few things to note:

- Names follow Rust conventions: `msg_type` becomes `MsgType`, and `msg` becomes `Msg`.
- Byte fields such as `mac: [u8; 6]` and `text: Tail` become `&'i [u8]` (byte slices)
  that *borrow* from the input buffer, so parsing them is zero-copy.
- Integer fields such as `value: u16` and `timestamp: u32` become native Rust integers, so
  parsing them would perform "small" copies. Vest does this because
  1. integers might be mis-aligned in wire and attempting to read them directly would be `unsafe`, and
  2. integer types are small and cheap enough to copy (`size_of::<u16>()` is 2 bytes, while `size_of::<&u16>()` is 8 or 4 bytes)
- The `choose` becomes a Rust enum, `MsgContent`, named after the struct and the
  field it appears in. Each variant holds one of our content structs.
- Each named definition gets its own *format type*, such as `ReadingFmt`. This is a zero-sized type
  that implements certain traits to provide the parser, serializer, as well as the specifications and proofs for that format.
  In this tutorial, we'll only need `MsgFmt`, which handles the whole message.

The [Construct-to-Rust mapping](dsl/mapping.md) shows how every DSL construct corresponds to a Rust type.

## Parsing a message

Now it's time to parse some bytes! Replace the contents of `src/main.rs` with this program:

```rust,ignore
mod msg;

use msg::*;
use vest_lib::core::exec::Parser;

fn main() {
    let wire: &[u8] = &[
        0x02,                   // tag       = 2 (Reading)
        0x07, 0x00,             // len       = 7
        0x03,                   // sensor    = 3
        0x66, 0x08,             // value     = 2150 (0x0866)
        0x00, 0xF1, 0x53, 0x65, // timestamp = 1700000000 (0x6553F100)
    ];

    let (consumed, msg) = MsgFmt.parse(&wire).unwrap();
    println!("consumed {consumed} bytes: {msg:?}");
}
```

Notice the byte order: because integers are little-endian, `value = 0x0866` is
stored as `66 08`, with the least significant byte first.

Run it with `cargo run`, and you should see:

```text
consumed 10 bytes: Msg { tag: Reading, len: 7, content: Reading(Reading { sensor: 3, value: 2150, timestamp: 1700000000 }) }
```

`parse` returns a pair when it succeeds: how many bytes it consumed, and the parsed value.
In general, Vest doesn't require full consumption of the input. If
you're reading messages from a stream, the count tells you where the next
message begins.

The parsed value is an ordinary Rust value, so you can inspect it however you
like:

```rust,ignore
assert_eq!(consumed, 10);
assert_eq!(msg.tag, MsgType::Reading);
assert_eq!(msg.len, 7);
assert_eq!(msg.content, MsgContent::Reading(Reading { sensor: 3, value: 2150, timestamp: 1700000000 }));
```

### Try breaking the parser

Let's poke at the parser with some bad input. We'll make a mutable copy of the
message, change it, and parse it again:

```rust,ignore
let mut bad = wire.to_vec();
bad[0] = 0x04; // not a valid tag
println!("{:?}", MsgFmt.parse(&bad.as_slice()));
```

Here's what happens for this change and a few others:

| Change to `bad` | Result |
| --- | --- |
| `bad[0] = 0x04` (an unknown tag) | `Err(ParseError { kind: InvalidTag, failed_format: Some("msg_type") })` |
| `bad[1] = 0x06` (a `len` too short for a `reading`) | `Err(ParseError { kind: UnexpectedEof, failed_format: Some("reading") })` |
| `bad[1] = 0x08` and `bad.push(0xFF)` (one byte more than a `reading` actually consumes) | `Err(ParseError { kind: LengthMismatch, failed_format: None })` |
| `bad.truncate(8)` (a message cut short) | `Err(ParseError { kind: UnexpectedEof, failed_format: None })` |
| `bad.extend([0xFF, 0xFF])` (extra bytes after the message) | `Ok(...)`, with `consumed` still 10 |

Every malformed input produced an error that the caller can handle.
In fact, no input can make the parser panic, read out of bounds, or loop forever: these are among
the properties [Vest proves](guarantees.md).

## Serializing a message

In Vest, serializing a value according to a binary format normally takes two steps:

1. `prepare` checks that the value is fully compliant with the format and computes how
   many bytes it will take on the wire.
2. `serialize` writes the value into a buffer of exactly that size.

Let's first bring the relevant traits into scope:

```rust,ignore
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};
```

Then serialize the message we just parsed:

```rust,ignore
let len = MsgFmt.prepare(&msg).unwrap(); // might fail if the value is inconsistent with the format or the length is too large
let mut output = vec![0u8; len];
MsgFmt.serialize(&msg, &mut output);
assert_eq!(output, wire);
```

We get back exactly the bytes we started with.

Why does Vest separate preparation from serialization? There are several key benefits:
1. *Infallible serialization*: It allows the caller to check for potential errors (such as a value that doesn't satisfy the format's constraints or integer overflows) before allocating a buffer. A fallible serialization would instead perform the checks while writing to the buffer, which could lead to partial writes and more complex error handling.
2. *Zero-reallocation*: It allows the caller to pre-allocate a buffer of the (provably) correct size, which can be more efficient than growing a buffer during serialization.

> **Always call `prepare` first.** Because `serialize` is designed to be infallible,
> it doesn't recheck the value or the
> buffer size; it relies on what `prepare` has already established. In ordinary
> Rust, nothing enforces this. If you skip `prepare`, the output is not
> guaranteed to match the format, and an undersized buffer may cause undefined
> behavior. In verified code, Verus prevents you from calling `serialize` without first establishing those proof obligations.

### Building a message from scratch

Apart from parsed values, we can also build the same message by hand and serialize it:

```rust,ignore
let fresh = Msg {
    tag: MsgType::Reading,
    len: 7, // sensor + value + timestamp = 1 + 2 + 4 bytes
    content: MsgContent::Reading(Reading { sensor: 3, value: 2150, timestamp: 1700000000 }),
};

let len = MsgFmt.prepare(&fresh).unwrap();
assert_eq!(len, 10); // 3 header bytes + 7 content bytes

let mut output = vec![0u8; len];
MsgFmt.serialize(&fresh, &mut output);
assert_eq!(output, wire); // the same bytes we parsed earlier
```

### When `prepare` fails

What if a value breaks the format's constraints?

```rust,ignore
let wrong_len = Msg { len: 99, ..fresh };
println!("{:?}", MsgFmt.prepare(&wrong_len));
```

`prepare` refuses:

```text
Err(PreSerializeError { kind: NotCompliant(LengthInconsistent), failed_format: None })
```

A tag that doesn't match the content is rejected too:

```rust,ignore
let wrong_tag = Msg { tag: MsgType::Log, ..fresh }; // the content is a Reading
println!("{:?}", MsgFmt.prepare(&wrong_tag));
```

```text
Err(PreSerializeError { kind: NotCompliant(InvalidTag), failed_format: Some("msg_content") })
```

Here, format dependencies work in the opposite direction. When parsing, `@tag` and
`@len` *decide* how to read the content. When serializing, they are
*constraints* that the value has to satisfy, and `prepare` is where Vest checks
them. Without that check, you could send a header that misdescribes its content,
and the receiver would misread the message.

## Checking the proofs (recommended)

So far, we've used `src/msg.rs` as ordinary Rust. The file also contains
*specifications* of what the parser and serializer should do, together with
*proofs* that they are functionally correct and secure with respect to the specification.

Technically, you don't need Verus to use Vest. If you're working in unverified Rust and just
want to parse and serialize more safely, you can stop here. Still, we highly
recommend checking the proofs with Verus. That way, you don't have to trust the
Vest DSL compiler: Verus confirms that the generated code really satisfies the
[promised properties](guarantees.md).

Each Vest release works with one exact Verus release, recorded in
[`verus.json`](https://github.com/secure-foundations/vest/blob/main/verus.json).
Follow the [Verus installation instructions](https://github.com/verus-lang/verus/blob/main/INSTALL.md)
for that version, or let a script from the Vest repository install it for you:

```console
git clone https://github.com/secure-foundations/vest.git
./vest/scripts/install-verus.sh
export PATH="$PWD/vest/.verus:$PATH"
```

Next, add this section to your crate's `Cargo.toml` so that `cargo verus` knows
to verify it:

```toml
[package.metadata.verus]
verify = true
```

Then, from your project directory, run:

```console
cargo verus verify
```

Verus checks in order `vstd`, `vest_lib`, and then your crate, which can take a minute or
two. Each one prints a line like this:

```text
verification results:: 121 verified, 0 errors
```

When you see `0` verification errors, all of the proofs in the generated module
have been checked, and congrats that Vest's guarantees hold for your format and its generated
parser and serializer.

## Using Vest from verified Rust

So far, we've called the generated code from ordinary Rust. If your application
is also verified with Verus, it can go one step further and use Vest's theorems
in its own proofs. Real applications can be more complex, but here's a small
example: a function that proves that parsing a serialized value gives back the
original value.

```rust,ignore
use crate::msg::*; // Vest-generated module
use vest_lib::prelude::*; // Bring the `vest_lib` specification and proof traits into scope

verus! {

fn roundtrip(value: &Msg<'_>) -> Result<(), PreSerializeError> {
    let len = MsgFmt.prepare(value)?;
    let mut output = vec![0u8; len];
    MsgFmt.serialize(value, &mut output);

    proof {
        MsgFmt.theorem_serialize_parse_roundtrip(value.deep_view()); // invoke Vest-provided theorem in Verus's proof block
    }
    let (consumed, parsed) = MsgFmt.parse(&output.as_slice()).unwrap();
    assert(consumed == len); // Verus assertion
    assert(parsed.deep_view() == value.deep_view());
    Ok(())
}

} // verus!
```

Let's walk through it:

1. `prepare` checks that the value is consistent with the format and tells us
   exactly how much space to allocate for the serialized output, just like before.
2. `serialize` fills that space with the value's binary encoding. Here, Verus
   verifies that the value is consistent and the buffer has exactly the required size (because we just called `prepare`).
3. The `proof` block calls Vest's roundtrip theorem. It tells Verus that
   parsing `output` (the serialized `value`) succeeds, consumes all `len` bytes, and returns the same
   logical contents. That's enough for Verus to prove both `assert`s, and to
   prove that the `unwrap` can never panic.

Note that the `proof` block and the Verus `assert(...)` statements are checked at compile time and add no work
at run time. Use Rust's `assert!(...)` if you also want a check at run time.

In the above example, we used Vest's theorem to reason about the values abstractly/symbolically.
To prove more subtle facts about particular fields, or to work out concrete serialized lengths, see
[Reasoning about generated values](dsl/generated-api.md#reasoning-about-generated-values).

## Summary

Congratulations, you've built and verified your first Vest format! Along the
way, you've seen how to:

- describe a binary format with enums, structs, dependencies (`@`), bounded
  regions (`[u8; @len] >>= ...`), and choices (`choose`);
- compile it with `vest` and use the generated types from Rust;
- parse with `parse`, which returns the parsed value and how many bytes it
  consumed when successful, or an error when it fails;
- serialize with `prepare` followed by `serialize`, and in particular, how
  `prepare` efficiently checks that the value is consistent with the format and computes the
  exact number of bytes needed for serialization;
- check the generated proofs with `cargo verus verify`, and use Vest's theorems
  in your own verified code.

## Where next

- [What Vest proves](guarantees.md): Vest's formal guarantees in detail.
- [Language reference](dsl/reference.md): every format construct in the Vest DSL, and the
  current limitations.
- [Generated Rust Code](dsl/generated-api.md): the full shape of what comes out of the DSL compiler,
  including more of the generated API and reasoning about values in Verus proofs.
- [ASN.1 compiler](asn1/index.md): generate DER or BER codecs from an ASN.1
  module instead of writing a `.vest` file.
