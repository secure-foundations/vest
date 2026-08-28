# VPS verified combinator library

This crate is the main verified backend of VPS. It provides executable parsers
and serializers together with specifications and machine-checked proofs of
their composition properties.

## Code map

- [`src/core/`](src/core/) defines the specification, proof, parser,
  serializer, preparation, byte-length, input, and output interfaces.
- [`src/combinators/`](src/combinators/) contains reusable combinators for
  sequencing, choice, mapping, refinement, repetition, termination, recursion,
  integers, bytes, and bit fields.
- [`src/primitives/`](src/primitives/) contains common primitive formats.
- [`src/asn1/`](src/asn1/) builds ASN.1 BER and DER formats from the combinator
  library.
- [`src/cbor/`](src/cbor/) implements generic CBOR and deterministic CBOR.

Most combinators are split into `spec`, `proof`, and `exec` files. The
specification describes the accepted bytes and serialized output. The proof
module establishes properties needed for safe composition. The executable
module implements the parser and serializer against those specifications.

The recursive combinator [`FixWith`](src/combinators/recursive/) separates a
recursive pure format from an efficient executable implementation. It is used
for formats such as recursive BER values and CBOR. Malleable formats, where
several byte strings represent the same value, expose the applicable
parse/serialize guarantees without claiming canonical parse-then-serialize
equality.

## Test and verify

```sh
cargo test
cargo verus verify -- --expand-errors
```

The CBOR integration tests in [`tests/cbor_rfc.rs`](tests/cbor_rfc.rs) exercise
examples and edge cases from RFC 8949. Generated ASN.1 tests live in the
separate [`vps-asn1`](../vps-asn1/) crate.
