# Examples and test corpus

The repository keeps source schemas beside generated, compiled, tested, and
verified Rust:

- [`vest_tests/src`](https://github.com/secure-foundations/vest/tree/main/vest_tests/src)
  contains DSL examples, including TLS, Bitcoin, bitfields, nested dependent
  lengths, recursion, and depth/width stress schemas.
- [`vest_asn1_tests`](https://github.com/secure-foundations/vest/tree/main/vest_asn1_tests)
  contains DER, BER, and mixed-rule ASN.1 fixtures.
- [`vest_dev/src/formats`](https://github.com/secure-foundations/vest/tree/main/vest_dev/src/formats)
  contains handwritten combinator examples and backend experiments.
- [`vest_lib/tests/cbor_rfc.rs`](https://github.com/secure-foundations/vest/blob/main/vest_lib/tests/cbor_rfc.rs)
  exercises RFC 8949 examples and documented deterministic-profile gaps.

These fixtures are preferable to isolated snippets when learning advanced
format composition because CI checks their generation freshness, Rust behavior,
and Verus proofs.

