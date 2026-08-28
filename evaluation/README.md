# VPS USENIX Security evaluation

This directory contains the scripts, harnesses, raw logs, and derived tables used
for the VPS evaluation.  It is intentionally self-contained except for path
dependencies on the implementations being measured and the existing benchmark
corpora (which are too large to duplicate).

## Evaluation questions

1. What is the size and proof burden of the verified VPS backend?
2. How does VPS compare with the original Vest on identical TLS and Bitcoin
   formats, both in verification cost and runtime performance?
3. How does verification scale with format depth and width?
4. How do generated ASN.1/CMS and generic CBOR codecs compare with suitable
   open-source Rust implementations?

Only semantically comparable baselines will appear in headline tables.  A
baseline is excluded (with the reason recorded) if it accepts a different wire
language, performs only recognition while VPS materializes values, or cannot be
configured to use an equivalent allocation policy.

## Layout

- `scripts/`: measurement and report-generation programs.
- `harnesses/`: unified runtime benchmark crates (added incrementally).
- `schemas/`: generated scalability inputs and benchmark schemas.
- `results/raw/`: immutable command output and profiler artifacts.
- `results/derived/`: CSV, JSON, and Markdown tables derived from raw data.

## Quick start

```sh
make stats
make plots
make machine-info
make manifest
make verify-backend THREADS=10
make cbor-real-runtime
make cms-real-runtime
```

All commands should be run from this directory. Verification measurements touch
`vps-lib/src/lib.rs` before running so Verus does not reuse cached verification.
They deliberately do not run `cargo clean`.

## LOC methodology

`scripts/loc_stats.py` counts nonblank, non-comment Rust source lines tracked by
Git under `vps-lib/src`. It classifies lines lexically as:

- **specification**: `spec fn` bodies and contracts (`requires`, `ensures`,
  `decreases`, and loop invariants);
- **proof**: `proof fn` bodies and explicit `proof { ... }` blocks;
- **executable**: ordinary `fn` bodies;
- **declaration/shared**: datatypes, traits, implementations, attributes, and
  other declarations shared by specification and execution.

The primary proof-to-code ratio is `(specification + proof) / implementation`.
Shared declarations support all three categories, so we apportion them evenly
among specification, proof, and implementation (with deterministic one-line
rounding). The three reported columns therefore sum to total SLOC; the raw
lexical counts, including `shared_sloc`, remain in the generated CSV/JSON for
auditability. Separate `FRAMEWORK` (core, combinators, and primitives) and
`CASE_STUDIES` (ASN.1 and CBOR) subtotals avoid conflating reusable
infrastructure with its applications. This is a reproducible lexical metric,
not a claim that Rust/Verus syntax has a unique semantic LOC partition.

## Fairness controls

- Vest and VPS verification use the same Verus executable, `vstd` release
  (`0.0.0-2026-07-27-0206`), worker count, host, and generated format semantics.
  Toolchain versions are recorded. `make manifest` also records hashes
  for the schemas, benchmark sources, lockfiles, and shared fixture sources.
- Bitcoin and TLS are each measured in a one-module crate. `--verify-module`
  restricts proof VCs but does not stop Rust from type-checking sibling modules,
  so timing them in the aggregate `vest-dsl-vps/test` crate would be misleading.
- Runtime comparisons use a unified Criterion harness, the same input bytes,
  the same retained input set, preallocated output buffers, and move setup and
  cloning outside the timed region.
- Every table retains raw logs, command lines, anonymized machine metadata,
  and corpus hashes.

The unified Vest/VPS runtime harness is in `harnesses/vest-vps-runtime`. A fast
correctness and corpus-intersection check is:

```sh
cargo bench --manifest-path harnesses/vest-vps-runtime/Cargo.toml --bench vest_vps -- --test
```

Runtime bar charts are written to `results/figures/`. Each bar uses Criterion's
bootstrap median point estimate. Its `+/-` value is Criterion's bootstrap
standard-deviation point estimate; plots transform `time ± standard deviation`
through `throughput = bytes/time`, yielding asymmetric whiskers. ASN.1 reports a common BER parse corpus for all three
parsers and a separate comprehensive BER corpus for VPS and rasn.
Each raw runtime run includes `throughput.tsv`, preserving Criterion's exact byte denominator for
parse and serialization separately; throughput is computed as bytes divided by time. This matters
for malleable BER and CBOR inputs, whose normalized serialized output can be shorter than the
parsed corpus.

The real CMS evaluation has three separately reported strata: 223 official NIST PKITS signed
S/MIME cases, 74 European Commission DSS CAdES fixtures (including BER and multi-megabyte
objects), and seven independently checked RFC 4134 examples. Every timed stratum is the exact
three-way BER intersection accepted by VPS, rasn-cms, and RustCrypto-cms. PKITS is treated as
ordinary BER CMS: 91 otherwise well-formed messages contain a `CertificateSet` whose elements
are not in canonical DER `SET OF` order. Full upstream and
per-implementation acceptance counts, source revisions, licenses, and hashes are recorded in
`corpora/cms/ATTRIBUTION.md` and the per-corpus manifests.
The benchmark additionally reports a directly sampled combined group containing all 304 selected
messages and 12,363,328 bytes; it is not computed by summing the separate estimates.

Matched depth/width measurements are generated on demand. Depth is a chain of
single-field records, structure width is the number of `u8` fields in one
record, and choice width is the number of tag-disjoint `u8` alternatives. For example:

```sh
python3 scripts/scalability.py --kind depth --sizes 1 4 8 16
python3 scripts/scalability.py --kind struct --sizes 1 4 8 16
python3 scripts/scalability.py --kind choice --sizes 2 4 8 16 32 64
```
