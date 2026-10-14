# Vest benchmarks

`vest_bench` measures the throughput of Vest-generated parsers and serializers using [Criterion](https://crates.io/crates/criterion).
It provides two benchmark families:

- microformats compare Vest-generated codecs with hand-written Rust implementations that have the same value layout and wire behavior, and
- real formats compare Vest-generated codecs with existing unverified Rust libraries for TLS, Bitcoin, CMS, and CBOR.

See [Fairness rules](#fairness-rules) for how we ensure that the comparisons are fair and meaningful.

## Contents

- [Benchmarks](#benchmarks)
- [Results](#results)
- [Running](#running)
- [Code layout](#code-layout)
- [Profiling](#profiling)
- [Fairness rules](#fairness-rules)

## Benchmarks

| Corpus | Source | Baseline |
| --- | --- | --- |
| `micro` | Synthetic tables, bitfields, lists, and nested formats | Hand-written Rust with the same value layout and wire behavior |
| `tls` | 909 TLS 1.3 handshake messages captured from 16 public servers and Chrome | [Rustls 0.22](https://crates.io/crates/rustls/0.22.4)'s publicly exposed low-level (`internal`) message codec |
| `bitcoin` | 4 consecutive mainnet blocks with 15,848 transactions | [`bitcoin`](https://crates.io/crates/bitcoin)'s consensus codec |
| `cms` | 1,024 synthetic `ContentInfo` and 304 `SignedData` messages from NIST PKITS, European Commission DSS CAdES, and RFC 4134 | `rasn-cms`, RustCrypto `cms`, and, for `ContentInfo`, `cryptographic-message-syntax` |
| `cbor` |  1,536 fragmented synthetic values and 49 real vectors from IETF COSE Working Group | `ciborium`, native `cbor4ii`, and `minicbor-serde` where their value models and consumption checks support the corpus |

The sources, manifests, licenses, and selection rules for the corpora are under [corpora/](corpora/).

## Results

<!-- benchmark-results:start -->

Full results: [`2026-10-14.md`](results/2026-10-14.md).

| Setting | Value |
| --- | --- |
| Run | 20261014T023832Z-d0de44ce |
| CPU | Apple M3 Pro |
| RAM | 18 GiB |
| Platform | macOS-27.0.1-arm64-arm-64bit-Mach-O |
| Logical CPUs | 11 |
| Compiler | rustc 1.98.1 (48a229cea 2026-09-01) |
| Commit | e8f9c0c1426652249002b0d60183c217392ff691 |
| Uncommitted files | Yes |
| Source/corpus SHA256 | 94664535838b907f5a46bcbdf35ca633854d9474589f2b0fdcd19ac070049339 |
| Sampling | 100 samples; 3 s warmup; 5 s target |
| Process-order seed | 3804991242 |
| Coverage | 51 of 51 entries |
| Allocator | std::alloc::System; counted separately, without timing |

Ratios are Vest/baseline throughput. 95% intervals describe within-run sampling noise, not between-run variability.

### Microformats

#### Parse

| Format | Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- | --- |
| `bits` | Vest | 3,640.0 [3,635.3–3,642.8] | — |
| `bits` | hand-written | 4,991.8 [4,988.2–5,006.0] | 0.73× [0.73–0.73] |
| `bounded_list` | Vest | 6,158.7 [6,114.3–6,186.5] | — |
| `bounded_list` | hand-written | 6,581.8 [6,283.7–6,683.4] | 0.94× [0.92–0.98] |
| `nest` | Vest | 15,582.0 [15,336.7–15,684.1] | — |
| `nest` | hand-written | 20,685.9 [20,630.4–20,709.1] | 0.75× [0.74–0.76] |
| `table` | Vest | 25,880.5 [25,824.1–25,937.0] | — |
| `table` | hand-written | 26,180.7 [26,035.5–26,505.1] | 0.99× [0.98–0.99] |

#### Serialize

| Format | Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- | --- |
| `bits` | Vest | 5,294.9 [5,286.6–5,304.4] | — |
| `bits` | hand-written | 5,667.4 [5,659.8–5,672.9] | 0.93× [0.93–0.94] |
| `bounded_list` | Vest | 2,565.2 [2,560.1–2,572.7] | — |
| `bounded_list` | hand-written | 2,308.2 [2,296.4–2,321.9] | 1.11× [1.11–1.12] |
| `nest` | Vest | 25,429.2 [25,378.5–25,469.6] | — |
| `nest` | hand-written | 15,860.9 [15,691.2–15,969.4] | 1.60× [1.59–1.62] |
| `table` | Vest | 21,473.0 [21,439.4–21,506.5] | — |
| `table` | hand-written | 19,770.7 [19,718.0–19,801.8] | 1.09× [1.08–1.09] |

### bitcoin/blocks/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 4,523.8 [4,497.1–4,541.0] | — |
| rust-bitcoin | 1,512.5 [1,505.2–1,517.7] | 2.99× [2.97–3.01] |

### bitcoin/blocks/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 6,000.5 [5,984.6–6,015.8] | — |
| rust-bitcoin | 5,139.5 [5,123.5–5,153.7] | 1.17× [1.16–1.17] |

### cbor/cose/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 644.8 [643.6–645.5] | — |
| cbor4ii | 621.1 [618.6–622.8] | 1.04× [1.04–1.04] |
| ciborium | 217.7 [217.4–218.0] | 2.96× [2.96–2.97] |

### cbor/cose/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 919.9 [917.0–923.1] | — |
| cbor4ii | 473.0 [471.3–474.3] | 1.94× [1.94–1.95] |
| ciborium | 409.7 [407.9–410.3] | 2.25× [2.24–2.26] |

### cbor/synthetic/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 494.6 [493.8–495.0] | — |
| ciborium | 192.4 [191.6–193.7] | 2.57× [2.55–2.58] |
| minicbor-serde | 471.9 [471.2–472.7] | 1.05× [1.05–1.05] |

### cbor/synthetic/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 688.5 [683.8–690.7] | — |
| cbor4ii | 467.9 [466.3–469.6] | 1.47× [1.46–1.48] |
| ciborium | 386.6 [386.0–387.1] | 1.78× [1.77–1.79] |
| minicbor-serde | 488.5 [483.7–489.7] | 1.41× [1.40–1.42] |

### cms/content_info/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 4,434.9 [4,429.1–4,444.2] | — |
| RustCrypto-cms | 2,895.9 [2,891.0–2,905.8] | 1.53× [1.53–1.54] |
| cryptographic-message-syntax | 3,642.4 [3,636.0–3,647.8] | 1.22× [1.22–1.22] |
| rasn-cms | 3,152.6 [3,137.8–3,180.2] | 1.41× [1.39–1.41] |

### cms/content_info/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 5,433.1 [5,417.0–5,441.3] | — |
| RustCrypto-cms | 5,798.5 [5,788.3–5,819.1] | 0.94× [0.93–0.94] |
| cryptographic-message-syntax | 16,144.3 [16,065.4–16,215.0] | 0.34× [0.33–0.34] |
| rasn-cms | 1,077.3 [1,074.0–1,079.4] | 5.04× [5.03–5.06] |

### cms/real_signed_data/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 5,875.9 [5,856.2–5,895.3] | — |
| RustCrypto-cms | 2,735.6 [2,716.1–2,744.4] | 2.15× [2.14–2.16] |
| rasn-cms | 2,893.2 [2,856.1–2,954.3] | 2.03× [1.99–2.06] |

### cms/real_signed_data/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 2,673.6 [2,665.7–2,679.9] | — |
| RustCrypto-cms | 5,056.9 [5,032.4–5,069.2] | 0.53× [0.53–0.53] |
| rasn-cms | 1,141.2 [1,130.7–1,163.4] | 2.34× [2.30–2.37] |

### tls/handshakes/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 7,310.7 [7,244.7–7,403.0] | — |
| Rustls | 3,494.5 [3,490.0–3,498.9] | 2.09× [2.07–2.12] |

### tls/handshakes/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 10,925.9 [10,849.1–11,007.3] | — |
| Rustls | 3,636.2 [3,631.8–3,642.7] | 3.00× [2.98–3.03] |


<!-- benchmark-results:end -->

## Running

Run these commands from `vest_bench/`. Rust and Python 3.10 or later must be
available; Cargo uses the workspace's locked dependencies and bench profile.

### Build and check

```console
make generate  # regenerate all microformat Rust codecs from their .vest files
make list      # list each workload with item and input-byte counts
make smoke     # compile all benchmarks and check their corpora, without timing
make test      # run Rust tests and Python runner/report tests
```

### Measure and report

```console
make bench                      # measure everything and audit allocations
make report                     # print the latest full-suite results
make report REPORT_ARGS=--write  # regenerate results/<date>.md and this README
```

The full suite has 51 entries across 10 workloads. Each entry processes its whole
corpus, using 100 samples, three seconds of warmup, and a five-second measurement
target. That budgets at least 6 minutes 48 seconds, plus builds, corpus checks,
and statistical analysis. Criterion may extend a measurement to collect enough
samples. Run on an idle machine; avoid other benchmarks or builds. Preparation,
result lifetime, and output-buffer policies are described in [Fairness rules](#fairness-rules).

Each implementation/operation runs in a separate process, in randomized order.
The manifest records the order seed, machine, compiler, commit, uncommitted-file
status, source/corpus fingerprint, settings, and coverage. Allocation audits use
a separate instrumented build and do not affect throughput timings. Tests are a
separate step; the measurement runner does not invoke `make test`.

### Select work and inspect runs

`scripts/bench.py` provides `list`, `run`, and `report`. The Makefile forwards
`TARGETS` to all three commands, and `LIST_ARGS`, `RUN_ARGS`, or `REPORT_ARGS`
to the corresponding command. Prefixes match complete ID components:

```console
make list TARGETS="tls micro/bits"
make bench TARGETS=tls RUN_ARGS="--seed 1234"
make bench TARGETS="micro/bits/serialize"  # both implementations
make report TARGETS=tls                 # filter the latest full-suite report
python3 -B scripts/bench.py run --quick micro/bits
python3 -B scripts/bench.py report --run /absolute/path/printed/by/the/runner
```

A full measurement ID is `family/workload/operation/implementation`, such as
`bitcoin/blocks/parse/rust-bitcoin`. Prefixes can select a family (`bitcoin`),
workload (`bitcoin/blocks`), operation (`bitcoin/blocks/parse`), or implementation
(the full ID).
Reports name the implementations available for each workload. Selecting one
implementation reports its timings without a comparison ratio.

| Option | Command | Meaning |
| --- | --- | --- |
| `--timeout SECONDS` | `list`, `run` | Per-process limit for inventory, measurement, and each family's allocation audit; default 300 seconds, not a total-run limit |
| `--seed N` | `run` | Fix process order for repeatability; otherwise a generated seed is recorded |
| `--allocations` | `run` | Collect untimed allocation counts after measuring; `make bench` includes this |
| `--quick` | `run` | Validation-only settings: 10 samples, 0.1-second warmup, 0.2-second target; cannot publish README tables |
| `--run PATH` | `report` | Read a specific run directory instead of the latest full-suite run |
| `--write` | `report` | Generate the detailed dated results and README tables from the same complete, current-source, whole-suite, non-quick run |

Use `python3 -B scripts/bench.py <command> --help` for command-line help.
For timings without the allocation audit, use
`python3 -B scripts/bench.py run tls`. To use only cached Cargo dependencies,
set `CARGO_NET_OFFLINE=true`, for example `CARGO_NET_OFFLINE=true make bench`.

Run directories are under `../target/vest-bench/runs/`. Each contains
`run.json`, `criterion/` raw samples, and `logs/` process output. Only completed,
unfiltered, non-quick runs update `latest.json`. Selected and quick runs print
their directory; inspect them with `--run PATH`. `make report TARGETS=tls`
filters the latest full-suite run—it does not choose a newer TLS-only run.
Reports never fill missing results from another run and reject incomplete runs
and unequal comparison workloads. Source/corpus fingerprints must match; rerun
the benchmarks after changes. The runner reads only its current manifest format.

`--write` requires hardware metadata and no source changes since measurement.
Uncommitted sources are allowed and clearly recorded; committing first makes
the measured revision easier to reproduce. The result file is marked
auto-generated. Do not hand-edit it or the generated block above.

## Code layout

| Location | Contents |
| --- | --- |
| `benches/*.rs` | Criterion entry points for each format |
| `src/harness.rs`, `src/allocations.rs` | Shared timing routines, inventory, and separate allocation audit |
| `src/micro/<format>/` | `.vest` microformats, generated codec, hand-written codec, and synthetic values |
| `src/real/` | Real format corpus loaders and baseline parser and serializer adapters |
| `corpora/` | Checked-in inputs, manifests, selection rules, and attribution |
| `tests/` | Rust wire/corpus checks and Python runner/reporting regressions |
| `scripts/bench.py` | Python runner and report generator |
| `results/` | Auto-generated measurements |

## Profiling

Build the usual bench profile with debug symbols, then attach Instruments,
`samply`, or `perf` to a selected Criterion workload:

```console
CARGO_PROFILE_BENCH_DEBUG=true cargo bench -p vest_bench --bench cms -- \
  --profile-time 10 'cms/real_signed_data/serialize/Vest'
```

## Fairness rules

For microformats, both Vest-produced and handwritten parsers read the same byte slices into equivalent Rust
types with matching field layouts, size, and alignment.
Both borrow byte payloads without copying and allocate collections where needed.
Parsed values are stored in an outer vector allocated before timing and dropped after timing
(such that deallocation is not timed as part of parsing).
Both serializers calculate their exact output length inside timing, then write in
place into reusable `&mut [u8]` buffers initialized outside timing.
Results on both sides are passed to `black_box`.
Compile-time assertions check size and alignment; `tests/micro.rs` checks full consumption and byte-identical encodings from both codecs.

For real formats, parsers translate the same byte inputs into their libraries'
native value types; layouts and ownership need not match (which mimics real-world usage).
Vest's parsers borrow supported payloads; collections allocate, and fragmented
BER/CBOR strings are flattened into owned storage.

The pinned Rustls handshake, rust-bitcoin `Block`, rasn-CMS, and RustCrypto CMS types own their
payloads; none has a borrowing-mode switch. `cbor4ii::core::Value` and
`ciborium::Value` also contain `Vec<u8>`/`String`, so they cannot borrow.
The minicbor-serde comparison decodes into `ciborium::Value`. cbor4ii and
minicbor support borrowed fields in custom types, but that would require another
value model and benchmark, which we leave for future work.

Native parsing work also differs: RustCrypto retains CMS eContent as
`Any`, while Vest and rasn fully parse and flatten it; bcder's synthetic
`ContentInfo` captures the inner content without decoding its schema.

For serialization, the benchmarks measure the throughput of *realistic* usage patterns, which may differ among libraries.
Only implementations that support computing the exact length before the actual serialization may reuse a pre-sized output buffer.
The others allocate a fresh output for every value and pay for its growth (which is fair, because the API does not allow the caller to preallocate).
Final outputs are retained until the timer stops; serializers' temporary allocation and destruction (if any) are timed.

| Implementation | Timed serialization |
| --- | --- |
| Vest | `prepare` to validate and calculate length, then `serialize` into a reusable, initialized slice |
| Hand-written microformats | `size`, then write into a reusable, initialized slice |
| RustCrypto CMS | `encoded_len`, then `encode_to_slice` into a reusable, initialized slice |
| rust-bitcoin | `total_size`, clear/reserve the reusable vector, then `consensus_encode` |
| bcder / cryptographic-message-syntax | `Values::encoded_len`, clear/reserve the reusable vector, then `write_encoded` |
| Rustls | `Vec::new()`, then `encode` |
| rasn | `rasn::der::encode` (that produces a `Vec<u8>`) |
| ciborium, native cbor4ii, minicbor-serde | Start from `Vec::new()`, then encode |

Before measurement, tests and corpus checks validate full input consumption,
parsed contents, and matching serialized bytes.
Diagnostic tracing (`vest_lib/error-trace`) is rejected,
including when another workspace dependency enables it. Allocation audits use
a separate counting build; the timed binaries use the uninstrumented system
allocator.

We found two baseline limitations during the benchmark development:

- `cryptographic-message-syntax` 0.28.0 omits the `ContentInfo` `[0] EXPLICIT`
  wrapper when encoding. The benchmark builds the correct wrapper with public
  bcder combinators, including that work in the timed loop. Issue filed: https://github.com/indygreg/cryptography-rs/issues/99
- `cbor4ii` 1.2.3 leaves indefinite-string break bytes unread. It is excluded
  from fragmented-input parsing, but included in real COSE parsing and in
  serialization, where the consumption and output checks pass. Issue filed: https://github.com/quininer/cbor4ii/issues/60
