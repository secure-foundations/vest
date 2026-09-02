# Introducing Vest 2.0

Since the last year, we've been pondering the design and implementation of Vest to make it more expressive, flexible, scalable, and easier to use, all while keeping strong correctness, security, and performance guarantees.

The result is **Vest 2.0**, a complete redesign of the combinator library that achieves better composability and more flexible security guarantees, as well as a more powerful DSL and its compiler that admits a wider range of formats.

With Vest 2.0, we also built a new ASN.1 compiler that automatically compiles `.asn1` modules into verified Rust codecs supporting both
Distinguished Encoding Rules (DER) and Basic Encoding Rules (BER).
The generated codecs compose our verified ASN.1 primitives as well as Vest combinators, so they enjoy the same correctness and security guarantees as Vest DSL formats.

We also built a verified prototype for both general and deterministic CBOR (RFC 8949), and we are working on a more complete support for it (e.g., canonical map keys and code generation from CDDL schemas).

## DSL Highlights

To users, perhaps the most exciting part of Vest 2.0 is the enhanced DSL and its compiler:

- We added support for _bitfields_ (bit-sized integers, bit-sized enums, and constraints on bitfields).
- We added initial support for (mutually) _recursive_ formats (still highly experimental).
- `enum`s now can come with refinements; you can also specify `const` enum values.
- `Vec` and `Option` fields now compose better with the rest of the format.
- We added the stack-allocated array (as opposed to the heap-allocated `Vec`) format `[fmt; N]` to specify repeated elements with a statically known count.
- We added the `Nothing` and `Never` formats, which are useful in combination with structs and choices.
- We added support for (nested) _field access_ expressions and basic _length_ expressions.
- We added support for a limited form of refinement types for parameterized formats.
- We added better _error reporting_ mechanisms and sometimes you can add custom error messages.
- We improved the quality of the DSL-generated code, making both the _executable and verification performance_ better. The emitted code is also more modular, documented, readable, and closer to idiomatic Rust.

## Migrating from Vest 1.0 to Vest 2.0

### Recompile your `.vest` files

Generated Vest 1.0 modules are not compatible with the new `vest_lib` and hence the `.vest` formats must be recompiled with the Vest 2.0 compiler.

The core Vest 1.0 DSL grammar is retained, so _most_ `.vest` files can be recompiled without changes.
However, the DSL compiler in Vest 2.0 is not completely backwards-compatible: dependent `choose` expressions must now be _exhaustive_. If a Vest
1.0 choice intentionally rejected every unlisted tag, add an explicit branch:

```vest
body: choose(@tag) {
    1 => request,
    2 => response,
    _ => Never("unknown message tag"),
}
```

### Update calls to generated parsers and serializers

Vest 1.0 emitted three executable functions for a
definition such as `packet`:

```rust,ignore
let (consumed, packet) = parse_packet(input)?;
let len = packet_len(&packet);
let mut output = vec![0u8; len];
serialize_packet(&packet, &mut output, 0)?;
```

Vest 2.0 instead emits a nominal format type named `PacketFmt`.
Parsing and serialization are trait methods on that type.

```rust,ignore
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

let (consumed, packet) = PacketFmt.parse(&input)?;
let len = PacketFmt.prepare(&packet)?;
let mut output = vec![0u8; len];
PacketFmt.serialize(&packet, &mut output);
```

Note that:

1. `prepare` is a new API that dynamically checks the value for consistency with the format and provably computes its exact wire-length. In Vest 1.0, users must explicitly prove that **(1)** the value is valid, and **(2)** the wire-length is `<= usize::MAX`, which can be quite onerous for complex formats.
2. `serialize` now only takes an output buffer without a position argument, which makes it more ergonomic to use. It now also does _not_ fail: a `prepare`d value is guaranteed to be serializable into a buffer of the exact length returned by `prepare`.

To summarize, the primary API changes are:

| Vest 1.0                                             | Vest 2.0                                                                                  |
| ---------------------------------------------------- | ----------------------------------------------------------------------------------------- |
| `packet()` / `PacketCombinator.spec_XXX/theorem_XXX` | `PacketFmt.spec_XXX/theorem_XXX`                                                          |
| `parse_packet(input)?`                               | `PacketFmt.parse(&input)?`                                                                |
| `packet_len(&value)`                                 | `PacketFmt.prepare(&value)?`, which validates the value and returns its exact byte length |
| `serialize_packet(&value, &mut vec, pos)?`           | `PacketFmt.serialize(&value, &mut slice)`                                                 |

See the [generated API guide](guide/src/dsl/generated-api.md) for a more complete description of the generated code.

### Handwritten `vest_lib` formats

The `vest_lib` trait hierarchy and combinators were completely redesigned.
Authors of handwritten formats
should follow the current [`vest_lib` documentation](https://secure-foundations.github.io/vest/vest_lib/)
and the examples in [`vest_dev/src/formats`](vest_dev/src/formats) for guidance on how to implement them in Vest 2.0.

---

Please give Vest 2.0 a try! Update both `vest` and `vest_lib` to the 0.2 release and use
the Verus release recorded in [`verus.json`](verus.json).
