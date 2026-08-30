# Vest DSL tutorial

This tutorial builds a length-prefixed packet whose payload borrows from the
input.

## Install the tools

Clone Vest and install the pinned Verus release:

```console
git clone --filter=blob:none https://github.com/secure-foundations/vest.git
cd vest
./scripts/install-verus.sh
export PATH="$PWD/.verus:$PATH"
cargo build --release -p vest
```

Applications using generated code also depend on the matching `vest_lib` and
`vstd` versions. The workspace manifest is the authoritative compatibility
record.

## Describe the wire format

Create `packet.vest`:

```vest
!BIG_ENDIAN

packet = {
    @len: u16,
    payload: [u8; @len],
}
```

The `@len` field appears on the wire but is a dependency rather than a field in
the logical structural suffix. The payload length is checked against it during
parsing and preparation.

Generate Rust:

```console
target/release/vest packet.vest --output packet.rs
```

The generated file contains the executable value type `Packet`, the nominal
format `PacketFmt`, pure specifications, and compositional proofs.

## Parse and serialize

With the generated module in scope, use the backend traits directly:

```rust,ignore
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

let input: &[u8] = &[0, 3, b'a', b'b', b'c'];
let (consumed, packet) = PacketFmt.parse(&input).unwrap();
assert_eq!(consumed, input.len());
assert_eq!(packet.payload, b"abc");

let len = PacketFmt.prepare(&packet).unwrap();
let mut output = vec![0; len];
PacketFmt.serialize(&packet, output.as_mut_slice());
assert_eq!(output, input);
```

`prepare` validates the value and returns its exact serialized length. The
in-place `serialize` API therefore needs no temporary output allocation. Parse
results include the number of bytes consumed, so callers can decide whether
trailing input is permitted.

Continue with the [language reference](reference.md) and the
[generated API guide](generated-api.md). Larger verified examples live in the
[test corpus](../examples.md).
