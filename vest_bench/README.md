# Vest benchmarks

`vest_bench` measures the throughput of Vest-generated parsers and serializers using [Criterion](https://crates.io/crates/criterion).
It provides two benchmark families:

- microformats compare Vest-generated codecs with hand-written Rust implementations that have the same value layout and wire behavior, and
- real formats compare Vest-generated codecs with existing unverified Rust libraries for TLS, Bitcoin, CMS, and CBOR.

Each timed iteration processes a complete corpus. Parsing builds decoded values
and retains them until the timer stops; serialization includes Vest's `prepare`
and the baseline's own sizing or allocation work. Loading inputs, constructing
serializer values, checking correctness, and dropping final results are untimed.
All formats report byte throughput and time per corpus pass; the report also
shows latency per item. Buffer reuse and ownership follow the rules below; see
[Fairness rules](#fairness-rules).

## Contents

- [Benchmarks](#benchmarks)
- [Results](#results)
  - [Machine and settings](#machine-and-settings)
  - [Microformats](#microformats)
  - [TLS](#tls)
  - [Bitcoin](#bitcoin)
  - [CMS](#cms)
  - [CBOR](#cbor)
  - [Allocation behavior](#allocation-behavior)
- [Running](#running)
- [Code layout](#code-layout)
- [Profiling CMS](#profiling-cms)
- [Fairness rules](#fairness-rules)

## Benchmarks

| Corpus | Source | Baseline |
| --- | --- | --- |
| `formats`: eight microformats | Synthetic structs, repetition, nesting, TLV, varints, bits, bounded lists, and tail lists | Hand-written Rust with the same value layout and wire behavior |
| `tls`: 909 TLS 1.3 handshake messages | Captures from 16 public servers and Chrome, grouped by message type | [Rustls 0.22](https://crates.io/crates/rustls/0.22.4)'s publicly exposed low-level (`internal`) message codec |
| `bitcoin`: four blocks, 15,848 transactions | Consecutive mainnet blocks | [`bitcoin`](https://crates.io/crates/bitcoin)'s consensus codec |
| `cms`: 1,024 synthetic `ContentInfo` and 304 real `SignedData` messages | Synthetic inputs; NIST PKITS, European Commission DSS CAdES, and RFC 4134 | `rasn-cms`, RustCrypto `cms`, and, for `ContentInfo`, `cryptographic-message-syntax` |
| `cbor`: 1,536 synthetic values in fragmented and definite encodings, plus 49 real vectors | Synthetic inputs; IETF COSE Working Group | `ciborium`, native `cbor4ii`, and `minicbor-serde` where their value models and consumption checks support the corpus |

The sources, manifests, licenses, and selection rules for the corpora are under [corpora/](corpora/).

## Results

These are historical measurements from October 10, 2026. That version capped
unknown-length repetitions at 32 initially reserved elements as well as 16 KiB.
The current code retains only the 16 KiB byte cap; it has not been re-measured.
The tables below do not report performance of the current reservation policy.

### Machine and settings

| Setting | Value |
| --- | --- |
| Machine | Apple M3 Pro, 11 cores (5 performance + 6 efficiency), 18 GiB RAM |
| OS | macOS 27.0.1 |
| Compiler | Rust 1.97.1 |
| Build | Bench profile: optimization level 3, fat LTO, one codegen unit |
| Sampling | Criterion 0.5.1; 100 samples, 3-second warmup, 5-second target measurement per entry |
| Isolation | One implementation/workload per process, randomized order with a recorded seed |
| Allocator | `std::alloc::System`; allocation counts collected separately, without timing |
| Recorded run | October 10, 2026; process-order seed `2614067746` |

The [complete results and allocation counts](results/2026-10-10.md) include the
source/corpus fingerprint used for these tables.
The [October 9 snapshot](results/2026-10-09.md) predates the reservation change; see the
[CMS profiling and reservation investigation](results/2026-10-10-cms-and-reservations.md)
for that change and the encoder cost breakdown.

Results use median time per corpus pass, with throughput derived from that time
and 95% confidence intervals in brackets. All ratios divide Vest's throughput by
the baseline's throughput: above 1× means Vest is faster.
Ratio intervals use independent bootstrap resampling of each implementation's
samples. They capture sampling noise, not variation between runs or machines.

### Microformats

Times are microseconds (µs) per corpus pass; throughput is MiB/s.

**Parse**

| Format | Vest (µs) | Hand-written (µs) | Vest (MiB/s) | Hand (MiB/s) | Vest/hand |
| --- | ---: | ---: | ---: | ---: | ---: |
| `flat` | 37.88 [37.84–37.91] | 30.15 [30.12–30.19] | 44,928.2 | 56,447.2 | 0.80× [0.79–0.80] |
| `table` | 36.48 [36.41–36.65] | 37.25 [37.17–37.33] | 28,392.8 | 27,806.0 | 1.02× [1.02–1.02] |
| `bounded_list` | 172.79 [171.96–174.06] | 205.90 [204.09–208.67] | 9,547.2 | 8,012.3 | 1.19× [1.18–1.21] |
| `tail_list` | 170.30 [169.61–171.67] | 189.77 [187.73–191.71] | 9,575.2 | 8,592.5 | 1.11× [1.10–1.13] |
| `nest` | 101.61 [101.30–101.86] | 81.29 [81.13–81.40] | 17,644.8 | 22,054.8 | 0.80× [0.80–0.80] |
| `tlv` | 33.44 [33.27–33.52] | 26.10 [26.01–26.14] | 5,732.4 | 7,344.8 | 0.78× [0.78–0.78] |
| `varint` | 140.92 [140.12–142.16] | 117.97 [117.68–118.29] | 22,019.6 | 26,302.3 | 0.84× [0.83–0.84] |
| `bits` | 81.16 [80.22–82.14] | 63.10 [62.95–63.22] | 4,230.2 | 5,440.7 | 0.78× [0.77–0.79] |

**Serialize**

| Format | Vest (µs) | Hand-written (µs) | Vest (MiB/s) | Hand (MiB/s) | Vest/hand |
| --- | ---: | ---: | ---: | ---: | ---: |
| `flat` | 45.02 [44.95–45.10] | 47.61 [47.54–47.72] | 37,805.3 | 35,747.5 | 1.06× [1.06–1.06] |
| `table` | 46.47 [46.37–46.61] | 48.94 [48.87–49.06] | 22,286.4 | 21,164.5 | 1.05× [1.05–1.06] |
| `bounded_list` | 619.20 [615.52–621.68] | 658.11 [655.82–659.75] | 2,664.2 | 2,506.7 | 1.06× [1.06–1.07] |
| `tail_list` | 632.75 [630.19–635.03] | 648.60 [646.29–651.05] | 2,577.0 | 2,514.1 | 1.03× [1.02–1.03] |
| `nest` | 54.25 [54.05–54.54] | 66.10 [65.95–66.41] | 33,048.6 | 27,123.6 | 1.22× [1.21–1.23] |
| `tlv` | 35.28 [35.15–35.39] | 31.04 [30.78–31.21] | 5,433.5 | 6,176.5 | 0.88× [0.87–0.89] |
| `varint` | 213.64 [210.46–219.93] | 224.82 [222.27–226.91] | 14,524.4 | 13,801.6 | 1.05× [1.02–1.07] |
| `bits` | 47.76 [47.45–47.86] | 41.30 [41.25–41.34] | 7,188.8 | 8,313.3 | 0.86× [0.86–0.87] |

### TLS

**Parse (MiB/s)**

| Message | Vest | Rustls | Vest/Rustls |
| --- | ---: | ---: | ---: | ---: |
| ClientHello | 2,973.3 [2,967.7–2,977.8] | 1,388.0 [1,384.7–1,390.1] | 2.14× [2.14–2.15] |
| ServerHello / HelloRetryRequest | 8,934.1 [8,898.4–8,997.2] | 4,683.1 [4,678.3–4,692.0] | 1.91× [1.90–1.92] |
| EncryptedExtensions | 622.6 [622.1–623.5] | 371.5 [371.3–372.2] | 1.68× [1.67–1.68] |
| Certificate | 66,177.9 [66,096.7–66,341.8] | 18,383.5 [18,370.5–18,422.0] | 3.60× [3.59–3.61] |
| CertificateVerify | 9,826.4 [9,819.1–9,845.3] | 3,510.1 [3,486.1–3,525.8] | 2.80× [2.79–2.82] |
| Finished | 3,393.9 [3,388.9–3,401.7] | 1,336.5 [1,320.8–1,340.3] | 2.54× [2.53–2.57] |
| NewSessionTicket | 8,767.1 [8,753.3–8,776.1] | 3,617.3 [3,609.1–3,624.1] | 2.42× [2.42–2.43] |

**Serialize (MiB/s)**

| Message | Vest | Rustls | Vest/Rustls |
| --- | ---: | ---: | ---: | ---: |
| ClientHello | 4,017.8 [4,002.8–4,028.9] | 2,158.6 [2,153.4–2,163.4] | 1.86× [1.85–1.87] |
| ServerHello / HelloRetryRequest | 11,372.1 [11,338.2–11,424.0] | 2,817.9 [2,809.5–2,825.1] | 4.04× [4.02–4.06] |
| EncryptedExtensions | 1,090.6 [1,090.0–1,091.8] | 352.9 [352.2–353.7] | 3.09× [3.08–3.10] |
| Certificate | 44,194.0 [44,112.4–44,264.5] | 12,640.5 [12,572.8–12,705.7] | 3.50× [3.48–3.51] |
| CertificateVerify | 16,263.2 [16,214.9–16,307.6] | 3,364.1 [3,341.3–3,386.6] | 4.83× [4.80–4.87] |
| Finished | 5,667.3 [5,654.8–5,695.1] | 1,092.2 [1,089.0–1,095.7] | 5.19× [5.17–5.22] |
| NewSessionTicket | 12,813.0 [12,763.6–12,854.9] | 1,864.9 [1,860.3–1,868.7] | 6.87× [6.84–6.90] |

### Bitcoin

| Implementation | Parse (MiB/s) | Serialize (MiB/s) | Vest/impl. (parse) | Vest/impl. (serialize) |
| --- | ---: | ---: | ---: | ---: |
| Vest | 5,220.9 [5,209.4–5,233.6] | 6,098.6 [6,031.5–6,144.6] | — | — |
| rust-bitcoin | 1,541.8 [1,531.3–1,548.0] | 5,447.2 [5,422.2–5,468.1] | 3.39× [3.37–3.41] | 1.12× [1.11–1.13] |

### CMS

**Synthetic ContentInfo: 1,024 messages**

| Implementation | Parse (MiB/s) | Serialize (MiB/s) | Vest/impl. (parse) | Vest/impl. (serialize) |
| --- | ---: | ---: | ---: | ---: |
| Vest | 4,512.2 [4,491.2–4,522.0] | 4,403.0 [4,372.9–4,447.0] | — | — |
| rasn-cms | 3,124.2 [3,116.7–3,131.8] | 1,070.9 [1,067.6–1,074.4] | 1.44× [1.44–1.45] | 4.11× [4.08–4.15] |
| RustCrypto-cms | 2,629.5 [2,617.2–2,637.6] | 5,740.8 [5,697.9–5,777.9] | 1.72× [1.71–1.73] | 0.77× [0.76–0.78] |
| cryptographic-message-syntax | 3,692.1 [3,687.4–3,698.8] | 12,758.3 [12,711.7–12,782.6] | 1.22× [1.22–1.23] | 0.35× [0.34–0.35] |

**Real SignedData: 304 messages from NIST PKITS, EC DSS CAdES, and RFC 4134**

| Implementation | Parse (MiB/s) | Serialize (MiB/s) | Vest/impl. (parse) | Vest/impl. (serialize) |
| --- | ---: | ---: | ---: | ---: |
| Vest | 6,547.6 [6,507.5–6,561.3] | 3,179.9 [3,121.2–3,243.1] | — | — |
| rasn-cms | 3,190.8 [3,176.5–3,214.9] | 1,377.0 [1,374.9–1,379.6] | 2.05× [2.03–2.06] | 2.31× [2.26–2.36] |
| RustCrypto-cms | 2,917.3 [2,891.0–2,952.6] | 5,880.2 [5,867.2–5,891.9] | 2.24× [2.21–2.27] | 0.54× [0.53–0.55] |

### CBOR

**Synthetic fragmented inputs: 1,536 values**

| Implementation | Parse (MiB/s) | Serialize (MiB/s) | Vest/impl. (parse) | Vest/impl. (serialize) |
| --- | ---: | ---: | ---: | ---: |
| Vest | 525.3 [524.4–526.4] | 720.3 [719.4–722.1] | — | — |
| ciborium | 208.0 [207.7–208.2] | 397.1 [394.4–398.3] | 2.53× [2.52–2.53] | 1.81× [1.81–1.83] |
| cbor4ii | — | 481.2 [473.4–485.5] | — | 1.50× [1.48–1.53] |
| minicbor-serde | 490.1 [486.4–492.0] | 511.6 [510.3–513.5] | 1.07× [1.07–1.08] | 1.41× [1.40–1.41] |

**Synthetic definite inputs: the same 1,536 values**

| Implementation | Parse (MiB/s) | Serialize (MiB/s) | Vest/impl. (parse) | Vest/impl. (serialize) |
| --- | ---: | ---: | ---: | ---: |
| Vest | 492.9 [491.6–494.2] | 717.5 [716.1–719.6] | — | — |
| ciborium | 177.6 [177.3–178.0] | 393.3 [392.1–395.3] | 2.78× [2.77–2.78] | 1.82× [1.81–1.83] |
| cbor4ii | 491.0 [489.6–493.6] | 479.9 [478.7–481.4] | 1.00× [1.00–1.01] | 1.49× [1.49–1.50] |
| minicbor-serde | 374.6 [372.7–375.9] | 508.5 [506.2–510.7] | 1.32× [1.31–1.32] | 1.41× [1.40–1.42] |

**Real COSE vectors: 49 values**

| Implementation | Parse (MiB/s) | Serialize (MiB/s) | Vest/impl. (parse) | Vest/impl. (serialize) |
| --- | ---: | ---: | ---: | ---: |
| Vest | 673.2 [671.6–674.7] | 944.8 [941.1–947.7] | — | — |
| ciborium | 228.5 [227.4–229.8] | 429.9 [428.4–431.0] | 2.95× [2.93–2.96] | 2.20× [2.19–2.21] |
| cbor4ii | 670.2 [669.0–670.8] | 492.6 [488.7–494.4] | 1.00× [1.00–1.01] | 1.92× [1.91–1.93] |

### Allocation behavior

The separate, untimed audit reports allocator calls and cumulative requested bytes,
not peak RSS. It excludes harness result storage and final result destruction.
All Vest serializers made zero allocations during preparation and writing.

In the historical run, the reservation change reduced CMS parsing requests from 4.46 GiB to 20.6 MiB,
TLS Certificate requests by 22×, and fragmented CBOR requests by 2.8×. For Bitcoin,
bounded initial reservation adds 28 growth operations and increases cumulative
requests from 7.04 to 9.38 MiB. See the
[reservation investigation](results/2026-10-10-cms-and-reservations.md) and
[complete per-entry audit](results/2026-10-10.md#untimed-allocation-audit).

## Running

From this directory:

```console
make generate       # regenerate microformat modules from formats/*.vest
make test           # layout parity, wire compatibility, and real-corpus validation
make smoke          # compile all benchmarks and execute each setup once
make bench          # run every benchmark and a separate allocation audit
make bench-formats  # only Vest-versus-hand-written microformats
make bench-real     # only TLS, Bitcoin, CMS, and CBOR
make report         # report the latest complete, source-matched run
```

Individual targets can also be run directly:

```console
cargo bench -p vest_bench --bench tls
cargo bench -p vest_bench --bench bitcoin
cargo bench -p vest_bench --bench cms
cargo bench -p vest_bench --bench cbor
```

Managed runs start a separate process for each implementation/workload, in
randomized order. Override `FORMATS` or `TARGETS` to select a subset:

```console
make bench-formats FORMATS="bounded_list tail_list"
make report TARGETS="bounded_list tail_list"
make bench TARGETS="tls cms"
```

`make report` does not rerun benchmarks. It reads only the latest completed run
under `../target/vest-bench/runs/`, including its raw Criterion samples, logs,
machine settings, source/corpus hashes, process order, and allocation counts.
It rejects partial runs, altered measurements, and source changes. A subset run
contains only that subset; it does not borrow missing results from earlier runs.
Quick runs have a separate pointer and never replace the latest performance run.

To inspect a specific historical run or make a short validation run:

```console
make report REPORT_ARGS="--run /path/to/run --allow-stale"
python3 -B scripts/run.py --quick --allocations cbor
python3 -B scripts/run.py --seed 1234 tls
python3 -B scripts/run.py --list cms
make bench TARGETS=cms RUN_ARGS="--offline --seed 1234"
```

Quick runs are clearly labeled and are not used for the tables above. Direct
`cargo bench` commands do not produce a managed manifest; inspect those results
explicitly with `python3 -B scripts/report.py --criterion-dir ../target/criterion`.

## Code layout

| Location | Contents |
| --- | --- |
| `benches/*.rs` | Timed comparisons, one target per format family |
| `benches/shared/` | Timing policy, allocation audit, protocol adapters and correctness checks |
| `src/generated/` | Microformat codecs emitted from `formats/*.vest` |
| `src/micro/` | Matching hand-written codecs, synthetic values and serialization passes |
| `src/corpora.rs`, `corpora/` | Captured TLS/Bitcoin loaders and checked-in inputs with provenance |
| `scripts/` | Run isolation, reporting, profiling and provenance checks |
| `tests/`, `scripts/tests/` | Codec/corpus checks and script regression tests |
| `results/` | Dated measurement snapshots and investigations |

## Profiling CMS

```console
python3 -B scripts/profile_cms.py
python3 -B scripts/profile_cms.py --sample  # macOS; permission to sample child processes required
```

The diagnostic uses the same inputs and normalization as the CMS benchmark.
It separates Vest preparation, length calculation and writing, and RustCrypto
length calculation and writing. Rasn exposes a combined encoding operation.
`total` follows the benchmark's sizing/allocation policy; `write` uses cached
lengths only to isolate the writing cost. Setup and final output destruction
are untimed. Phase medians do not necessarily add up to the combined median.

Profiles, logs, phase measurements, source hashes and machine information are
saved under `../target/vest-bench/profiles/`. The profiling build uses the bench
optimization settings plus debug symbols. Sampling can perturb measurements;
use unsampled runs for phase timings. Reported percentiles are not confidence
intervals. The separate `micro_profile` example includes destruction and
is intended only for locating hot code, not throughput comparisons.

## Fairness rules

For microformats, both parsers read the same byte slices into equivalent Rust
types with matching field layouts, size, and alignment. Both borrow byte payloads
without copying and allocate collections where needed. Decoded values are stored
in an outer vector allocated before timing and dropped after timing. Both
serializers calculate their exact output length inside timing, then write in
place into reusable `&mut [u8]` buffers initialized outside timing; no zero-filling
or resizing is timed. `layout_parity` checks size and alignment;
`wire_compat` checks byte-identical output, cross-parser acceptance, and matching
validation behavior. Results on both sides are passed to `black_box`.

For real formats, every parser receives the same bytes but returns its library's
native value type, not a forced common layout. Vest uses partial zero-copy parsing:
its TLS and Bitcoin types borrow byte fields; its CMS types borrow supported
payloads and opaque values;
`CborValue<'i>` borrows definite byte/text strings. Collections still allocate,
and fragmented BER/CBOR strings are flattened into owned storage. The Rustls,
rust-bitcoin, and CMS baseline types used here own their data. `cbor4ii` uses its
owned native `core::Value`; `ciborium` and `minicbor-serde` use owned
`ciborium::Value`. Ciborium reuses a caller-provided 4 KiB scratch buffer, avoiding
per-call initialization. These are the APIs measured, even
where a library also offers borrowing APIs. Native decoding work can differ:
for example, RustCrypto retains CMS eContent as `Any`, while Vest and rasn decode
and flatten it; bcder's synthetic `ContentInfo` decoder captures the inner content
without decoding its schema. Decoding and storing results are timed; destroying those
results is not. Rustls's owned input buffers are constructed once and reused;
the codec returns each input buffer to its owner after parsing.

Real-format serialization starts from equivalent values constructed and, for
CMS, normalized outside timing. Only an implementation that computes the exact
length **inside timing, before writing** may reuse a pre-sized output buffer.
The others allocate a fresh output for every value and pay for its growth.
Final outputs are retained until the timer stops; encoder-internal temporary
allocation and destruction remain timed.

| Implementation | Timed serialization |
| --- | --- |
| Vest | `prepare`, then `serialize` into a reusable, initialized slice |
| Hand-written microformats | `size_*`, then write into a reusable, initialized slice |
| RustCrypto CMS | `encoded_len`, then `encode_to_slice` into a reusable slice |
| rust-bitcoin | `total_size`, clear/reserve the reusable vector, then `consensus_encode` |
| bcder / cryptographic-message-syntax | `Values::encoded_len`, clear/reserve the reusable vector, then `write_encoded` |
| Rustls | `Vec::new()`, then `encode` |
| rasn | `rasn::der::encode`, including its output allocation |
| ciborium, native cbor4ii, minicbor-serde | Start from `Vec::new()`, then encode |

Before measurement, tests and corpus checks validate full input consumption,
decoded contents, and matching serialized bytes. Timed inputs and results are
passed to `black_box`. Diagnostic tracing (`vest_lib/error-trace`) is rejected,
including when another workspace dependency enables it. Allocation audits use
a separate counting build; the timed binaries use the uninstrumented system
allocator.

Two baseline limitations:

- `cryptographic-message-syntax` 0.28.0 omits the `ContentInfo` `[0] EXPLICIT`
  wrapper when encoding. The benchmark builds the correct wrapper with public
  bcder combinators, including that work in the timed loop. Issue filed: https://github.com/indygreg/cryptography-rs/issues/99
- `cbor4ii` 1.2.3 leaves indefinite-string break bytes unread. It is excluded
  from fragmented-input parsing, but included in the separate `synthetic_definite`
  comparison and in serialization, where the output checks pass. Issue filed: https://github.com/quininer/cbor4ii/issues/60
