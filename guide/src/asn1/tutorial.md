# ASN.1 tutorial

This walkthrough generates a small DER codec from an ASN.1 module and uses it to parse and serialize a message.

## Define a module

Create `message.asn1`:

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

## Generate DER

`vest_asn1` is currently a repository tool rather than a published crate:

```console
cargo run -p vest_asn1 -- message.asn1 -o src/message.rs
```

DER is the default. Use `--rules ber` for BER, or definition overrides for a
module with canonical DER substructures inside a BER envelope; see
[DER, BER, and rule overrides](index.md#der-ber-and-rule-overrides).

The generator emits `Kind` and `Packet<'i>` value types. Unlike the Vest DSL, their verified format
values are `KIND::Fmt` and `PACKET::Fmt`. Uppercase format names avoid collisions with the
idiomatic Rust value names. Tagged formats also store their effective tag to
support `IMPLICIT` retagging.

## Parse and serialize

```rust,ignore
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};
use crate::message::{Kind, PACKET};

let encoded: &[u8] = &[
    0x30, 0x07,             // SEQUENCE, seven content octets
    0x0a, 0x01, 0x00,       // Kind::Request
    0x80, 0x02, 0xaa, 0xbb, // [0] IMPLICIT OCTET STRING
];

let (consumed, packet) = PACKET::Fmt.parse(&encoded).unwrap();
assert_eq!(consumed, encoded.len());
assert_eq!(packet.kind, Kind::Request);
assert_eq!(packet.payload, Some(&[0xaa, 0xbb][..]));

let size = PACKET::Fmt.prepare(&packet).unwrap();
let mut output = vec![0u8; size];
PACKET::Fmt.serialize(&packet, &mut output);
assert_eq!(output, encoded);
```

DER byte strings and UTF-8-compatible character strings *borrow* from the input.
BER string formats concatenate constructed fragments into owned values.
`BMPString` and `UniversalString` are always owned because their wire encodings
must be converted to UTF-8.

## What is checked

**TODO.** Discuss the proof obligations for format non-ambiguity, etc.
