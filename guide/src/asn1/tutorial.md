# ASN.1 tutorial

In this tutorial, we'll generate a parser and a serializer from a small ASN.1
schema and use them in ordinary Rust and in Verus.
The overall workflow is much like the [Vest DSL](../getting-started.md).

## Setting up

Install Vest's ASN.1 compiler `vest_asn1` and create a Rust project:

```console
cargo install vest_asn1 --version 0.1.0 --locked
cargo new --lib asn1-example
cd asn1-example
```

Add the `vest_lib` and `vstd` dependencies from
[Setting up](../getting-started.md#create-a-project). This compiler release
uses `vest_lib` 0.2.3 and its matching Verus/vstd versions.

## Turn an ASN.1 schema into Rust

We'll define an ASN.1 module containing a message with a request/response kind and an optional payload of
1–32 bytes. Save this schema as `message.asn1` in the project directory:

```asn1
Message DEFINITIONS EXPLICIT TAGS ::= BEGIN
    Kind ::= ENUMERATED {
        request(0),
        response(1)
    }

    Packet ::= SEQUENCE {
        kind Kind,
        payload [0] IMPLICIT OCTET STRING (SIZE (1..32)) OPTIONAL
    }
END
```

The syntax is standard ASN.1, with a few restrictions documented in [ASN.1 support table](support.md).
Now we can generate a Rust module using `vest_asn1`, then add `pub mod message;` to `src/lib.rs` to expose it.
Invoke the compiler with:

```console
vest_asn1 message.asn1 -o src/message.rs
```

The default generated codec uses DER. For BER or mixed-rule schemas, see
[DER, BER, and rule overrides](index.md#der-ber-and-rule-overrides).

## Using the generated code

The compiler gives us ordinary Rust value types: `Kind` is an enum, and
`Packet<'i>` has `kind: Kind` and `payload: Option<&'i [u8]>` fields. The payload
borrows from the input when parsing, just like a byte field in the Vest DSL.

Each definition also gets a format type. Where the DSL uses a value such as
`PacketFmt`, the ASN.1 compiler uses `PACKET::Fmt`: an associated constant on
the format type `PACKET`. There're several reasons for doing it this way. One major reason
is that ASN.1 types can be (re-)tagged (`IMPLICIT`ly or `EXPLICIT`ly) in different contexts.
The emitted format `PACKET::Fmt` stores its default effective tag, and you can change it with, for example,
`vest_lib::asn1::der::IMPLICIT(3, PACKET::Fmt)` when you need a different tag.
We'll use the original tag here.

Now create `examples/roundtrip.rs` with this program:

```rust,ignore
use asn1_example::message::{Kind, Packet, PACKET};
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

fn main() {
    let packet = Packet {
        kind: Kind::Request,
        payload: Some(b"hello"),
    };

    let len = PACKET::Fmt.prepare(&packet).unwrap();
    let mut output = vec![0u8; len];
    PACKET::Fmt.serialize(&packet, &mut output);

    let (consumed, parsed) = PACKET::Fmt.parse(&output.as_slice()).unwrap();
    assert_eq!(consumed, output.len());
    assert_eq!(parsed.kind, packet.kind);
    assert_eq!(parsed.payload, packet.payload);
}
```

Run it with `cargo run --example roundtrip`. As in the DSL tutorial, `prepare`
checks that the value is consistent with the format and returns its exact
serialized length; `serialize` writes into a buffer of that size. An empty
payload, for example, would make `prepare` return an error because our schema
requires at least one byte when the payload is present. See
[Serializing a message](../getting-started.md#serializing-a-message) for why
preparation matters.

ASN.1 formats also expose an additional API `length(&value)` through the `ByteLen` trait. Unlike
`prepare`, it does *not* check format constraints or overflow (so it can be faster): use it only when you
already know that the value is valid and the encoded length fits in `usize`.

### Using the generated code in Verus

First, follow [Checking the proofs](../getting-started.md#checking-the-proofs-recommended)
to install the matching Verus release, enable verification in `Cargo.toml`,
and run `cargo verus verify`.

In general, Vest ASN.1 clients get to use the same set of Vest theorems as a DSL client.
Add this code to `src/lib.rs`, below `pub mod message;`:

```rust,ignore
use crate::message::{Packet, PACKET};
use vest_lib::prelude::*;

verus! {

pub fn roundtrip(value: &Packet<'_>) -> Result<(), PreSerializeError> {
    let len = PACKET::Fmt.prepare(value)?;
    let mut output = vec![0u8; len];
    PACKET::Fmt.serialize(value, &mut output);

    proof {
        PACKET::Fmt.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = PACKET::Fmt.parse(&output.as_slice()).unwrap();
    assert(consumed == len);
    assert(parsed.deep_view() == value.deep_view());

    proof {
        reveal(<Packet as DeepView>::deep_view);
    }
    assert(parsed.kind == value.kind);
    Ok(())
}

} // verus!
```

Run `cargo verus verify` again. The roundtrip theorem proves that parsing
succeeds, consumes every serialized byte, and returns the same logical value.
The last proof block opens `Packet`'s field-wise view so we can further assert
the equality of their `kind` fields. If you only need the abstract roundtrip property,
you can omit the last proof block and the `assert(parsed.kind == value.kind)` line.
These `assert(...)` statements are checked at verification time; use
`assert!(...)` for runtime checks.

For more on views, lengths, and other roundtrip theorems, see
[Reasoning about generated values](../dsl/generated-api.md#reasoning-about-generated-values).
The same `vest_lib` spec and proof traits apply here. In particular, DER formats
support non-malleability and parse–serialize roundtrip, while BER formats do not because they may accept
multiple encodings of one value.
