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

Full results: [`2026-10-13.md`](results/2026-10-13.md).

| Setting | Value |
| --- | --- |
| Run | 20261013T004105Z-f99c375f |
| CPU | Apple M3 Pro |
| RAM | 18 GiB |
| Platform | macOS-27.0.1-arm64-arm-64bit-Mach-O |
| Logical CPUs | 11 |
| Compiler | rustc 1.97.1 (8bab26f4f 2026-07-14) |
| Commit | 450a71641aff9fc1a1d68b8746f681e658970f3a |
| Uncommitted files | Yes |
| Source/corpus SHA256 | 434212a696aec08a4a5f5008b4f20f92e4079bfd360e5e1e35d617ad4846f856 |
| Sampling | 100 samples; 3 s warmup; 5 s target |
| Process-order seed | 1234 |
| Coverage | 51 of 51 entries |
| Allocator | std::alloc::System; counted separately, without timing |

Ratios are Vest/baseline throughput. 95% intervals describe within-run sampling noise, not between-run variability.

### Microformats

#### Parse

| Format | Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- | --- |
| `bits` | Vest | 3,868.4 [3,862.1–3,872.5] | — |
| `bits` | hand-written | 5,315.8 [5,310.0–5,326.1] | 0.73× [0.73–0.73] |
| `bounded_list` | Vest | 7,608.7 [7,592.2–7,644.5] | — |
| `bounded_list` | hand-written | 8,220.7 [8,183.9–8,247.0] | 0.93× [0.92–0.93] |
| `nest` | Vest | 16,613.6 [16,595.0–16,651.4] | — |
| `nest` | hand-written | 21,806.7 [21,764.9–21,839.9] | 0.76× [0.76–0.76] |
| `table` | Vest | 27,780.2 [27,734.2–27,814.1] | — |
| `table` | hand-written | 28,113.9 [28,065.2–28,151.3] | 0.99× [0.99–0.99] |

#### Serialize

| Format | Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- | --- |
| `bits` | Vest | 5,472.0 [5,465.4–5,478.6] | — |
| `bits` | hand-written | 5,656.5 [5,622.3–5,665.1] | 0.97× [0.97–0.97] |
| `bounded_list` | Vest | 2,659.8 [2,644.0–2,680.8] | — |
| `bounded_list` | hand-written | 2,488.1 [2,478.5–2,496.3] | 1.07× [1.06–1.08] |
| `nest` | Vest | 25,896.7 [25,868.6–25,921.2] | — |
| `nest` | hand-written | 19,735.9 [19,675.8–19,779.5] | 1.31× [1.31–1.32] |
| `table` | Vest | 22,307.1 [22,286.0–22,347.6] | — |
| `table` | hand-written | 21,074.9 [21,034.6–21,105.8] | 1.06× [1.06–1.06] |

### bitcoin/blocks/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 5,410.6 [5,404.7–5,425.5] | — |
| rust-bitcoin | 1,631.0 [1,627.5–1,633.1] | 3.32× [3.31–3.33] |

### bitcoin/blocks/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 6,450.1 [6,433.2–6,477.2] | — |
| rust-bitcoin | 5,311.5 [5,292.2–5,332.8] | 1.21× [1.21–1.22] |

### cbor/cose/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 663.7 [663.1–664.3] | — |
| cbor4ii | 653.3 [652.5–654.4] | 1.02× [1.01–1.02] |
| ciborium | 227.4 [227.2–227.6] | 2.92× [2.92–2.92] |

### cbor/cose/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 939.0 [937.1–939.9] | — |
| cbor4ii | 477.3 [475.8–480.6] | 1.97× [1.95–1.97] |
| ciborium | 431.9 [430.9–432.7] | 2.17× [2.17–2.18] |

### cbor/synthetic/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 517.3 [516.7–519.2] | — |
| ciborium | 210.0 [209.7–210.3] | 2.46× [2.46–2.47] |
| minicbor-serde | 493.2 [492.2–493.8] | 1.05× [1.05–1.05] |

### cbor/synthetic/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 728.7 [726.4–730.4] | — |
| cbor4ii | 491.1 [489.4–492.5] | 1.48× [1.48–1.49] |
| ciborium | 394.2 [393.2–396.0] | 1.85× [1.84–1.86] |
| minicbor-serde | 512.2 [511.3–514.3] | 1.42× [1.41–1.43] |

### cms/content_info/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 4,620.9 [4,614.3–4,625.0] | — |
| RustCrypto-cms | 2,831.5 [2,822.8–2,836.5] | 1.63× [1.63–1.64] |
| cryptographic-message-syntax | 3,861.4 [3,856.5–3,867.6] | 1.20× [1.19–1.20] |
| rasn-cms | 3,450.7 [3,444.4–3,453.4] | 1.34× [1.34–1.34] |

### cms/content_info/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 5,489.4 [5,465.5–5,505.2] | — |
| RustCrypto-cms | 6,118.4 [6,090.3–6,136.4] | 0.90× [0.89–0.90] |
| cryptographic-message-syntax | 18,269.1 [18,145.4–18,335.9] | 0.30× [0.30–0.30] |
| rasn-cms | 1,133.4 [1,131.1–1,137.2] | 4.84× [4.82–4.86] |

### cms/real_signed_data/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 6,513.3 [6,491.5–6,523.6] | — |
| RustCrypto-cms | 3,039.6 [3,031.9–3,043.3] | 2.14× [2.14–2.15] |
| rasn-cms | 3,259.3 [3,249.9–3,270.1] | 2.00× [1.99–2.01] |

### cms/real_signed_data/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 3,297.4 [3,285.6–3,312.7] | — |
| RustCrypto-cms | 5,410.1 [5,388.6–5,422.7] | 0.61× [0.61–0.61] |
| rasn-cms | 1,296.0 [1,291.2–1,301.5] | 2.54× [2.53–2.56] |

### tls/handshakes/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 7,980.2 [7,965.6–7,987.6] | — |
| Rustls | 3,729.4 [3,726.4–3,734.2] | 2.14× [2.14–2.14] |

### tls/handshakes/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 10,922.2 [10,898.1–10,940.4] | — |
| Rustls | 3,916.4 [3,906.4–3,922.5] | 2.79× [2.78–2.80] |


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
