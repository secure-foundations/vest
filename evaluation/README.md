# Reproducing the evaluation

This directory supports the paper's proof-effort, Vest comparison,
scalability, ASN.1/CMS, and CBOR results. Headline numbers are in
[`RESULTS.md`](RESULTS.md); comparison rules are in
[`BASELINES.md`](BASELINES.md).

`harnesses/` contains benchmark crates, `corpora/` records input provenance,
`scripts/` contains reproduction programs, and `results/` contains raw data,
generated tables, and figures.

## Rebuild the tables and paper figure

```sh
make stats
make paper-figure
```

The second command runs the paper's exact figure generator,
[`scripts/generate_eval_plots.py`](scripts/generate_eval_plots.py), and writes
`results/figures/eval_runtime.pdf`. These commands use checked-in measurements;
they do not rerun benchmarks.

## Rerun verification

```sh
make verify-backend THREADS=10
make verify-cases THREADS=10
```

Vest and VPS use the same Verus, `vstd`, thread count, machine, and input. TLS
and Bitcoin use separate one-module crates so unrelated Rust type checking is
not included.

## Rerun runtime benchmarks

```sh
make runtime-smoke
make runtime
make asn1-runtime
make cms-runtime
make cms-real-runtime
make cbor-runtime
make cbor-real-runtime
```

The harnesses check results before timing, reuse buffers, and exclude setup.
Real CMS comes from NIST PKITS, European Commission DSS, and RFC 4134; real
CBOR comes from IETF COSE examples. `corpora/` records versions, licenses,
hashes, and acceptance counts.

The full Bitcoin performance corpus is too large to store here. See
[`corpora/bitcoin/README.md`](corpora/bitcoin/README.md). It is not needed to
rebuild the checked-in tables or figure.

## Source-line counts

`scripts/loc_stats.py` counts nonblank, non-comment Rust lines. Shared
declarations are divided evenly among specification, proof, and implementation,
so those columns add to total lines. Framework code is reported separately from
the ASN.1 and CBOR case studies.
