# General and deterministic CBOR

`vest_lib::cbor::CborFmt<DET>` implements the RFC 8949 generic data model. Use
`CborFmt::<false>` for general well-formed CBOR and `CborFmt::<true>` for the
currently supported deterministic restrictions.

```rust,ignore
use vest_lib::cbor::CborFmt;
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

let input: &[u8] = &[0x82, 0x01, 0x02];
let (consumed, value) = CborFmt::<false>.parse(&input).unwrap();
assert_eq!(consumed, input.len());

let len = CborFmt::<false>.prepare(&value).unwrap();
let mut output = vec![0; len];
CborFmt::<false>.serialize(&value, output.as_mut_slice());
```

Definite byte and text strings borrow directly from the input. Fragmented
indefinite strings are flattened into owned values. Arrays, maps, tags, and
other recursive values use allocation and are bounded by the format's
recursion limit.

General CBOR accepts supported non-preferred argument widths and indefinite
containers; serialization normalizes those values to definite output. The
deterministic format additionally requires preferred integer, length, and tag
arguments and rejects indefinite-length items.

Deterministic map-key ordering and shortest-width floating-point normalization
are not yet enforced. Floating-point width is retained in the logical value,
and duplicate map keys are not rejected. Applications requiring those profile
rules must add a refinement or validation layer.

See the
[`cbor`](https://secure-foundations.github.io/vest/vest_lib/cbor/) API and the
RFC 8949 conformance tests under `vest_lib/tests/cbor_rfc.rs`.
