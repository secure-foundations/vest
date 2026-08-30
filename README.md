[![CI](https://github.com/secure-foundations/vest/actions/workflows/ci.yml/badge.svg)](https://github.com/secure-foundations/vest/actions/workflows/ci.yml)
[![Documentation](https://img.shields.io/badge/docs-vest__lib-blue)](https://secure-foundations.github.io/vest/vest_lib/)
[![Crates.io - vest](https://img.shields.io/crates/v/vest?label=vest)](https://crates.io/crates/vest)
[![Crates.io - vest_lib](https://img.shields.io/crates/v/vest_lib?label=vest_lib)](https://crates.io/crates/vest_lib)

# Vest

Vest generates fast, formally verified parsers and serializers for binary data
formats. It consists of a Verus combinator library and a DSL that compiles
concise format descriptions into safe Rust implementations, functional
specifications, and proofs.

Vest proves that generated code is memory-safe, panic-free, terminating, and
functionally correct. Formats may additionally establish parser soundness,
completeness, non-malleability, non-extensibility, serializer unambiguity, and
parser/serializer round trips. These properties are compositional: the library
proves them once for each combinator, and generated formats assemble those
proofs.

## Repository layout

- [`vest/`](vest/) — the `.vest` DSL compiler;
- [`vest_lib/`](vest_lib/) — verified parser and serializer combinators;
- [`vest_asn1/`](vest_asn1/) — an ASN.1 frontend targeting the same backend;
- [`vest_tests/`](vest_tests/) — DSL fixtures, including TLS and Bitcoin;
- [`vest_asn1_tests/`](vest_asn1_tests/) — generated DER, BER, and mixed-rule fixtures; and
- [`vest_dev/`](vest_dev/) — handwritten formats and development examples.

`vest_lib` includes primitive integer and byte formats, dependent and recursive
combinators, bitfields, a modular ASN.1 DER/BER backend, and a generic CBOR
codec. Its serializers write into caller-provided buffers and support
`core`-only, `alloc`, and `std` configurations.

## A small Vest format

```vest
!LITTLE_ENDIAN

message_type = enum {
    Request = 1,
    Response = 2,
}

message = {
    @kind: message_type,
    @len: u16,
    payload: [u8; @len],
}
```

The compiler emits Rust value types, executable parsing, preparation, length,
and serialization implementations, combinator specifications, and their
proofs. More examples are available beside their generated `.rs` files in
[`vest_tests/src/`](vest_tests/src/).

Build the compiler and generate Rust with:

```sh
cargo build --release -p vest
target/release/vest input.vest
```

Run `target/release/vest --help` for output and code-generation options. Vim
syntax highlighting is available in [`vest/vest.vim`](vest/vest.vim).

## ASN.1 and CBOR

The `vest_asn1` frontend generates verified nominal codecs from ASN.1 modules.
DER is the default; BER and per-definition rule overrides are also supported:

```sh
cargo run -p vest_asn1 -- schema.asn1 -o generated.rs
cargo run -p vest_asn1 -- --rules ber schema.asn1 -o generated_ber.rs
```

See [`vest_asn1/README.md`](vest_asn1/README.md) for the supported ASN.1 subset
and current limitations. The CBOR backend lives in
[`vest_lib/src/cbor/`](vest_lib/src/cbor/) and supports general and
deterministic CBOR codecs; deterministic map-key ordering is not yet enforced.

## Reproducible development setup

Install Rust, clone the repository, and install the pinned Verus release:

```sh
git clone --filter=blob:none https://github.com/secure-foundations/vest.git
cd vest
./scripts/install-verus.sh
export PATH="$PWD/.verus:$PATH"
```

The required Verus version is recorded in [`verus-version.txt`](verus-version.txt),
and the matching `vstd` version is pinned in the workspace manifest. Useful
commands include:

```sh
cargo test --workspace
cargo check -p vest_lib --no-default-features --all-targets
cargo check -p vest_lib --no-default-features --features alloc --all-targets
cargo verus verify -p vest_lib -- --expand-errors
cargo verus verify -p vest_tests -- --expand-errors
cargo verus verify -p vest_asn1_tests -- --expand-errors
```

Regenerate checked-in fixtures with `make -C vest_tests vest` and
`make -C vest_asn1_tests generate`. Vest-generated files use a curated
`verusfmt` list because formatting the deepest stress fixtures can stall.

See [CONTRIBUTING.md](CONTRIBUTING.md) for the complete development checks and
[CHANGELOG.md](CHANGELOG.md) for release history. A migration guide from Vest
1.x is coming soon. The final Vest 1.x source remains available on the
`vest-1.x` branch, and its published crate versions remain on crates.io.

## Publication

[Vest: Verified, Secure, High-Performance Parsing and Serialization for
Rust](https://tracycy.com/papers/vest-usenix-security25.pdf). Yi Cai, Pratap
Singh, Zhengyao Lin, Jay Bosamiya, Joshua Gancher, Milijana Surbatovich, and
Bryan Parno. USENIX Security, 2025.

```bibtex
@inproceedings{vest,
  author    = {Cai, Yi and Singh, Pratap and Lin, Zhengyao and Bosamiya, Jay and Gancher, Joshua and Surbatovich, Milijana and Parno, Bryan},
  booktitle = {Proceedings of the USENIX Security Symposium},
  month     = {August},
  title     = {{Vest}: Verified, Secure, High-Performance Parsing and Serialization for {Rust}},
  year      = {2025}
}
```

Vest is available under the MIT license.
