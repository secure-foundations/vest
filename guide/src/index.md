# Introduction

Vest generates secure, performant parsers and serializers for binary data
formats, formally verified in [Verus](https://github.com/verus-lang/verus).
It provides a concise format DSL for non-experts, as well as a combinator
library for experts who want to build formats directly in Verus.

Given a high-level format description, Vest automatically emits efficient, idiomatic Rust that is memory-safe, arithmetically safe, panic-free, and terminating on any input.
More importantly, Vest parsers and serializers are proven to satisfy a suite of desirable [security properties](guarantees.md), making them immune to entire classes of attacks that historically plague unverified, hand-written code.

With Vest, we have built the first
production-grade formally verified [ASN.1 library](asn1/index.md) (supporting both DER and BER, which we leverage to implement the first verified [CMS](https://github.com/secure-foundations/vest/blob/main/vest_asn1/rfcs/CMS-RFC5652-Curated.asn1) [codec](https://github.com/secure-foundations/vest/blob/main/vest_asn1_tests/src/generated_cms.rs)),
and a verified prototype for [both
general and deterministic CBOR](cbor.md).

## Who this is for

Vest is for anyone who needs to parse or serialize binary data formats, especially when correctness and security are critical. This includes:
*network security protocols* such as TLS and IKE, which parse handshake messages and serialize
authenticated responses; *cryptographic message formats* such as X.509 and CMS,
which encode certificates, signed objects, keys, and algorithm parameters; *executable and secure-update formats* carrying code alongside authenticated
metadata; and *RPC and distributed-systems* frameworks,
which marshal typed application objects onto wire formats such as Protocol Buffers.

Vest is still a research tool. It does not cover every format in the wild, and
[its current features and limitations are documented](dsl/reference.md).

As of now, this book covers the nitty-gritty of the DSL and the ASN.1 compiler. We are working on a guide to the underlying combinator library, as well as a more complete support for CBOR.

## Choose your path

| I want to… | Start here |
|---|---|
| install Vest and parse/serialize something | [Getting started](getting-started.md) |
| describe complex formats concisely | [Vest DSL language reference](dsl/reference.md) |
| understand what is actually proven | [What Vest proves](guarantees.md) |
| build a format using combinators | [Using `vest_lib`](library/combinators.md) |
| look up a trait or combinator in Vest | [`vest_lib` API reference](../vest_lib/index.html) |

The [project repository](https://github.com/secure-foundations/vest) holds the
source code for the combinator library, the DSL compiler, the ASN.1 library and frontend, and the CBOR codec.
