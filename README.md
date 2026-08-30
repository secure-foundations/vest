[![CI](https://github.com/secure-foundations/vest/actions/workflows/ci.yml/badge.svg)](https://github.com/secure-foundations/vest/actions/workflows/ci.yml)
[![Guide](https://img.shields.io/badge/docs-guide-blue)](https://secure-foundations.github.io/vest/guide/)
[![API](https://img.shields.io/badge/docs-vest__lib-blue)](https://secure-foundations.github.io/vest/vest_lib/)
[![Crates.io - vest](https://img.shields.io/crates/v/vest?label=vest)](https://crates.io/crates/vest)
[![Crates.io - vest_lib](https://img.shields.io/crates/v/vest_lib?label=vest_lib)](https://crates.io/crates/vest_lib)

# Vest

Vest generates fast, formally verified parsers and serializers for binary data
formats. It combines a concise format DSL with a Verus combinator library and
also provides verified ASN.1 and CBOR support.

Vest proves executable memory safety, panic freedom, termination, and
functional correctness. Formats can additionally establish round trips,
soundness, non-malleability, non-extensibility, and serializer unambiguity
through compositional proof interfaces.

## Choose an interface

| Task | Start here |
|---|---|
| Describe a binary protocol | [Vest DSL tutorial](https://secure-foundations.github.io/vest/guide/dsl/tutorial.html) |
| Generate DER or BER from ASN.1 | [ASN.1 frontend](https://secure-foundations.github.io/vest/guide/asn1/) |
| Compose formats directly in Verus | [`vest_lib` guide](https://secure-foundations.github.io/vest/guide/library/combinators.html) |
| Parse generic CBOR | [CBOR guide](https://secure-foundations.github.io/vest/guide/cbor.html) |
| Look up traits and combinators | [`vest_lib` API](https://secure-foundations.github.io/vest/vest_lib/) |

## A small Vest format

```vest
!BIG_ENDIAN

packet = {
    @len: u16,
    payload: [u8; @len],
}
```

Build the compiler and generate verified Rust:

```console
cargo install vest
vest packet.vest --output packet.rs
```

The generated module contains borrowing Rust value types, executable parsing,
preparation and in-place serialization, pure specifications, and proofs. See
the [tutorial](https://secure-foundations.github.io/vest/guide/dsl/tutorial.html)
for an end-to-end example.

## Components

- [`vest`](https://github.com/secure-foundations/vest/tree/main/vest) is the
  `.vest` compiler published on crates.io.
- [`vest_lib`](https://github.com/secure-foundations/vest/tree/main/vest_lib)
  is the verified backend, with `core`-only, `alloc`, and `std` configurations.
- [`vest_asn1`](https://github.com/secure-foundations/vest/tree/main/vest_asn1)
  generates nominal DER, BER, and mixed-rule formats.
- The generic CBOR codec is part of
  [`vest_lib::cbor`](https://secure-foundations.github.io/vest/vest_lib/cbor/).

Vest uses a pinned Verus release; the repository's
[`verus-version.txt`](https://github.com/secure-foundations/vest/blob/main/verus-version.txt)
and workspace manifest record the compatible toolchain and `vstd` version.

Vest was introduced in
[“Vest: Verified, Secure, High-Performance Parsing and Serialization for Rust”](https://tracycy.com/papers/vest-usenix-security25.pdf)
(USENIX Security 2025). Citation information is in the
[documentation](https://secure-foundations.github.io/vest/guide/citation.html).

Vest is available under the MIT license.
