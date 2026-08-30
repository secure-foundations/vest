# Vest documentation

Vest generates fast, formally verified parsers and serializers for binary data
formats. You can describe a format with the Vest DSL, generate codecs from an
ASN.1 schema, or compose the verified library directly.

Choose the path that matches your task:

| I want to… | Start here |
|---|---|
| describe a binary protocol concisely | [Vest DSL tutorial](dsl/tutorial.md) |
| understand the guarantees | [What Vest proves](guarantees.md) |
| build a format directly in Verus | [Using `vest_lib`](library/combinators.md) |
| generate DER or BER codecs | [ASN.1 frontend](asn1/index.md) |
| parse generic CBOR values | [CBOR guide](cbor.md) |
| look up a trait or combinator | [`vest_lib` API reference](https://secure-foundations.github.io/vest/vest_lib/) |

The [project repository](https://github.com/secure-foundations/vest) contains
the compiler, verified backend, generated TLS and Bitcoin case studies, ASN.1
fixtures, CBOR conformance tests, and the pinned Verus setup.

