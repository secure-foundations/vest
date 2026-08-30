# vest_lib

`vest_lib` is Vest's verified parser and serializer combinator library for
[Verus](https://github.com/verus-lang/verus). It provides functional
specifications, executable implementations, and compositional proofs for
binary formats.

The library includes:

- primitive byte, integer, bitfield, repetition, choice, mapping, refinement,
  dependent, and recursive combinators;
- allocation-free destination-passing serializers over caller-provided output
  buffers;
- `core`-only, `alloc`, and `std` feature configurations;
- ASN.1 DER and BER primitives and schema combinators; and
- general and deterministic CBOR formats.

The default feature is `std`. For smaller environments, use either
`default-features = false` or enable only `alloc`.

`vest_lib` is intended to be verified with the Verus version recorded in the
repository's `verus-version.txt`; its `vstd` dependency is pinned to the
corresponding release. Most users should describe formats with the `vest` DSL
or `vest_asn1` frontend instead of constructing large combinator types by hand.

See the [Vest repository](https://github.com/secure-foundations/vest) for setup,
examples, generated fixtures, and development commands. The detailed design
notes formerly kept here are available in
[`dev_docs/design.md`](dev_docs/design.md).
