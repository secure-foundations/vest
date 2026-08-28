# VPS

VPS builds verified binary parsers and serializers in Rust and Verus. This
repository contains the implementation and evaluation material for the paper.

## Paper-to-code guide

| Paper section | Source code |
|---|---|
| Design: malleability | [`combinators/choice`](vps-lib/src/combinators/choice/mod.rs) and [`combinators/mapped`](vps-lib/src/combinators/mapped/mod.rs) |
| Design: recursion | [`combinators/recursive/`](vps-lib/src/combinators/recursive/mod.rs) |
| Formalization and trait system | [`core/spec.rs`](vps-lib/src/core/spec.rs), [`core/proof.rs`](vps-lib/src/core/proof.rs) and [`combinators/`](vps-lib/src/combinators/mod.rs) |
| Efficient parser and serializer APIs | [`core/exec/`](vps-lib/src/core/exec/mod.rs) |
| ASN.1 BER, DER, and CMS case study | [`asn1/`](vps-lib/src/asn1/mod.rs), [`vps-asn1/`](vps-asn1/README.md), and the [`CMS schema`](vps-asn1/rfcs/CMS-RFC5652-Curated.asn1) |
| CBOR case study | [`cbor/`](vps-lib/src/cbor/mod.rs) |
| Evaluation | [`evaluation/README.md`](evaluation/README.md), [`RESULTS.md`](evaluation/RESULTS.md), and [`generate_eval_plots.py`](evaluation/scripts/generate_eval_plots.py) |

The TLS and Bitcoin case studies use the existing Vest language. The compiler
in `vest-dsl-vps/` ports that language to a backend that emits VPS combinators;
the language itself is not a contribution. `baselines/` contains the original
Vest implementation used in the paper's direct comparison.

## Test and verify

The project uses `cargo verus` and the `vstd` version pinned in each manifest.

```sh
cargo test --manifest-path vps-lib/Cargo.toml
cargo test --manifest-path vest-dsl-vps/Cargo.toml
cargo test --manifest-path vps-asn1/Cargo.toml

cd vps-lib
cargo verus verify -- --expand-errors
```

Generated-code suites can be rebuilt and verified with `make generate` and
`make verify` in `vest-dsl-vps/test/` and `vps-asn1/test/`.

## Reproduce the evaluation

See [`evaluation/README.md`](evaluation/README.md) for the short reproduction
commands. The large Bitcoin runtime input is not stored here; its checksum and
setup instructions are in
[`evaluation/corpora/bitcoin/README.md`](evaluation/corpora/bitcoin/README.md).
