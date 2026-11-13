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
| `cbor` | 1,536 fragmented synthetic values and 49 real vectors from IETF COSE Working Group | `ciborium`, plus native `cbor4ii` and `minicbor` adapters that build borrowing-aware ASTs |

The sources, manifests, licenses, and selection rules for the corpora are under [corpora/](corpora/).

## Results

<!-- benchmark-results:start -->

Full results: [`2026-11-12.md`](results/2026-11-12.md).

| Setting | Value |
| --- | --- |
| Run | 20261112T222529Z-625e567a |
| CPU | Apple M3 Pro |
| RAM | 18 GiB |
| Platform | macOS-27.0.1-arm64-arm-64bit-Mach-O |
| Logical CPUs | 11 |
| Compiler | rustc 1.99.1 (58cf8f9c3 2026-10-13) |
| Commit | 00583b9ae85a26a85815d8460200402a4b8922cf |
| Uncommitted files | Yes |
| Source/corpus SHA256 | 800c0fe2b1b9c504495c4c4d9a460337a8031771a1793148f0a6e985cc639851 |
| Sampling | 100 samples; 3 s warmup; 5 s target |
| Process-order seed | 1234 |
| Coverage | 54 of 54 entries |
| Allocator | std::alloc::System; counted separately, without timing |

Ratios are Vest/baseline throughput. 95% intervals describe within-run sampling noise, not between-run variability.

### Microformats

#### Parse

| Format | Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- | --- |
| `bits` | Vest | 3,658.0 [3,635.0–3,684.8] | — |
| `bits` | hand-written | 5,074.7 [5,061.5–5,101.6] | 0.72× [0.72–0.73] |
| `bounded_list` | Vest | 7,313.2 [6,985.4–7,550.4] | — |
| `bounded_list` | hand-written | 8,109.0 [7,939.0–8,200.9] | 0.90× [0.86–0.93] |
| `nest` | Vest | 16,140.8 [16,083.0–16,220.7] | — |
| `nest` | hand-written | 21,929.5 [21,813.0–21,979.0] | 0.74× [0.73–0.74] |
| `table` | Vest | 28,510.3 [28,472.8–28,537.7] | — |
| `table` | hand-written | 28,220.3 [28,154.9–28,273.7] | 1.01× [1.01–1.01] |

#### Serialize

| Format | Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- | --- |
| `bits` | Vest | 5,384.4 [5,364.3–5,407.8] | — |
| `bits` | hand-written | 5,654.6 [5,640.2–5,670.0] | 0.95× [0.95–0.96] |
| `bounded_list` | Vest | 2,762.2 [2,755.6–2,772.3] | — |
| `bounded_list` | hand-written | 2,676.3 [2,661.5–2,682.7] | 1.03× [1.03–1.04] |
| `nest` | Vest | 25,532.5 [25,423.3–25,617.5] | — |
| `nest` | hand-written | 19,566.4 [19,154.2–20,009.7] | 1.30× [1.28–1.33] |
| `table` | Vest | 22,585.9 [22,527.5–22,645.3] | — |
| `table` | hand-written | 21,265.0 [21,159.8–21,344.0] | 1.06× [1.06–1.07] |

### bitcoin/blocks/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 5,400.0 [5,294.9–5,459.6] | — |
| rust-bitcoin | 1,682.0 [1,680.3–1,683.9] | 3.21× [3.15–3.25] |

### bitcoin/blocks/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 6,758.8 [6,681.7–6,788.4] | — |
| rust-bitcoin | 5,570.7 [5,495.2–5,603.8] | 1.21× [1.20–1.23] |

### cbor/cose/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 968.5 [962.0–972.8] | — |
| cbor4ii | 924.0 [920.5–932.3] | 1.05× [1.04–1.05] |
| ciborium | 224.9 [223.4–226.1] | 4.31× [4.27–4.34] |
| minicbor | 499.9 [496.1–503.7] | 1.94× [1.92–1.95] |

### cbor/cose/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 909.7 [905.9–916.6] | — |
| cbor4ii | 460.8 [454.1–465.1] | 1.97× [1.96–2.00] |
| ciborium | 421.3 [418.4–423.5] | 2.16× [2.15–2.18] |
| minicbor | 517.8 [514.5–524.0] | 1.76× [1.74–1.77] |

### cbor/synthetic/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 628.3 [619.2–635.8] | — |
| cbor4ii | 693.9 [685.3–696.7] | 0.91× [0.89–0.92] |
| ciborium | 201.7 [198.4–203.4] | 3.12× [3.07–3.18] |
| minicbor | 553.0 [551.4–553.6] | 1.14× [1.12–1.15] |

### cbor/synthetic/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 702.4 [698.0–706.5] | — |
| cbor4ii | 442.2 [440.1–445.7] | 1.59× [1.57–1.60] |
| ciborium | 387.3 [382.7–391.1] | 1.81× [1.79–1.84] |
| minicbor | 450.2 [446.2–456.1] | 1.56× [1.54–1.58] |

### cms/content_info/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 4,630.2 [4,592.9–4,661.3] | — |
| RustCrypto-cms | 3,198.7 [3,180.4–3,211.9] | 1.45× [1.43–1.46] |
| cryptographic-message-syntax | 3,590.9 [3,574.6–3,622.0] | 1.29× [1.27–1.30] |
| rasn-cms | 3,399.3 [3,374.3–3,406.5] | 1.36× [1.35–1.38] |

### cms/content_info/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 5,414.9 [5,374.6–5,439.5] | — |
| RustCrypto-cms | 6,292.9 [6,248.9–6,308.5] | 0.86× [0.85–0.87] |
| cryptographic-message-syntax | 16,444.4 [16,364.2–16,522.0] | 0.33× [0.33–0.33] |
| rasn-cms | 1,132.4 [1,112.4–1,143.4] | 4.78× [4.72–4.87] |

### cms/real_signed_data/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 6,815.9 [6,796.5–6,827.9] | — |
| RustCrypto-cms | 2,996.1 [2,943.5–3,035.5] | 2.27× [2.24–2.32] |
| rasn-cms | 3,381.1 [3,373.1–3,385.2] | 2.02× [2.01–2.02] |

### cms/real_signed_data/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 3,375.6 [3,348.4–3,390.7] | — |
| RustCrypto-cms | 5,287.8 [5,255.6–5,337.4] | 0.64× [0.63–0.64] |
| rasn-cms | 1,298.4 [1,281.3–1,322.1] | 2.60× [2.55–2.63] |

### tls/handshakes/parse

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 8,160.2 [8,151.1–8,169.3] | — |
| Rustls | 3,688.7 [3,650.8–3,703.3] | 2.21× [2.20–2.24] |

### tls/handshakes/serialize

| Implementation | MiB/s [95% CI] | Vest/baseline [95% CI] |
| --- | --- | --- |
| Vest | 11,019.3 [10,967.4–11,075.6] | — |
| Rustls | 3,746.4 [3,733.5–3,773.4] | 2.94× [2.92–2.96] |


<!-- benchmark-results:end -->

## Running

Run these commands from `vest_bench/`. Rust and Python 3.10 or later must be
available; Cargo uses the workspace's locked dependencies and bench profile.
The runner and Makefile select the Rust version recorded in [`verus.json`](../verus.json),
matching the pinned Verus release.
That Rust toolchain must be installed with rustup; running benchmarks does not
require the Verus executable itself.

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

The full suite has 54 entries across 10 workloads. Each entry processes its whole
corpus, using 100 samples, three seconds of warmup, and a five-second measurement
target. That budgets at least 7 minutes 12 seconds, plus builds, corpus checks,
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
The pinned `rustls`, `rust-bitcoin`, `rasn-CMS`, `RustCrypto-CMS`, and `ciborium` only expose *owned*
types and hence do not support zero-copy.
`cbor4ii` and `minicbor` instead do provide native decoding traits to build selective zero-copy AST
(with `Cow` strings and bytes): definite strings borrow
from the input, fragmented strings/bytes are flattened into owned buffers.
Map order, duplicates, and tags are all preserved for CBOR parsers.

Native parsing work differs across ASN.1 libraries: RustCrypto retains CMS eContent as
`Any`, while Vest and rasn fully parse and flatten it; bcder's synthetic
`ContentInfo` captures the inner content without decoding its schema.

For serialization, the benchmarks measure the throughput of *realistic* usage patterns, which may differ among libraries.
Only implementations that support computing the exact length before the actual serialization may reuse a pre-sized output buffer.
The others allocate a fresh output for every value and pay for its dynamic growth (which is fair, because the API does not allow the caller to preallocate).
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
| ciborium | Start from `Vec::new()`, then encode |
| `cbor4ii` and `minicbor` | `encode` produces a `Vec<u8>` |

Before measurement, tests and corpus checks validate full input consumption,
parsed contents, and matching serialized bytes.
Diagnostic tracing (`vest_lib/error-trace`) is rejected,
including when another workspace dependency enables it. Allocation audits use
a separate counting build; the timed binaries use the uninstrumented system
allocator.

We found these baseline issues during benchmark development:

- `cryptographic-message-syntax` 0.28.0 omits the `ContentInfo` `[0] EXPLICIT`
  wrapper when encoding. The benchmark builds the correct wrapper with public
  bcder combinators, including that work in the timed loop. Issue filed: https://github.com/indygreg/cryptography-rs/issues/99
- `cbor4ii` 1.2.3 left indefinite-string break bytes unread. This was fixed
  upstream in 1.2.4, which this suite now uses for both synthetic and COSE
  parsing. Issue filed: https://github.com/quininer/cbor4ii/issues/60
