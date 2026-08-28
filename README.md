# VPS anonymous artifact

This repository is the anonymized artifact for the VPS paper. VPS is a
verified parser/serializer framework implemented in Rust and Verus. The
artifact contains the verified backend, the ASN.1 frontend and case studies,
the Vest DSL port used to generate VPS combinators, the original Vest baseline,
and the scripts and raw data supporting the evaluation.

The Vest DSL is not a contribution of this work. `vest-dsl-vps/` ports the
existing Vest DSL by implementing a custom code-generation backend that emits
VPS combinators. We retain the `.vest` extension and Vest terminology in that
frontend. “VPS” refers to the new verified backend and generated codecs.

## Repository layout

- `vps-lib/`: verified VPS core, combinators, primitives, ASN.1, and CBOR.
- `vest-dsl-vps/`: Vest DSL frontend with the VPS backend (`vest-vps`).
- `vps-asn1/`: ASN.1 frontend and curated schemas, including CMS.
- `evaluation/`: harnesses, scripts, corpora, raw logs, and derived results.
- `baselines/`: the original Vest library and DSL implementation used for the
  apple-to-apple comparison.

## Build and verify

The artifact expects the Verus-enabled Cargo command used by the paper’s
evaluation (`cargo verus`) and the pinned `vstd` version in each manifest.
From the repository root:

```sh
cargo check --manifest-path vps-lib/Cargo.toml
cargo test --manifest-path vest-dsl-vps/Cargo.toml
cargo test --manifest-path vps-asn1/Cargo.toml

cd vps-lib
cargo verus verify -- --expand-errors
```

To regenerate and verify the Vest DSL fixtures:

```sh
cd vest-dsl-vps/test
make generate
make verify
```

To regenerate and verify the ASN.1 fixtures:

```sh
cd vps-asn1/test
make generate
make verify
```

## Evaluation

See [`evaluation/README.md`](evaluation/README.md) for the methodology,
reproduction commands, fairness controls, corpus provenance, and organization
of raw and derived results. A quick non-mutating anonymity check is available
as:

```sh
scripts/audit-anonymity.sh
```

The full Bitcoin runtime corpus is intentionally not duplicated in the
anonymous snapshot because it exceeds the hosting service’s per-file limit.
Its expected SHA-256 digest and setup instructions are documented in the
evaluation directory; the bundled fixtures still support build, verification,
and smoke testing.

## Anonymity note

The historical system name “Vest” intentionally remains where it identifies
the published baseline or the source DSL. First-party author identities,
institutional links, local paths, repository history identifiers, and hostnames
are excluded from this branch.
