# CMS profiling and repetition reservation

This is a historical investigation of the October 10 measured version. The
current code retains the 16 KiB initial-reservation byte cap but no longer the
32-element cap for unknown-length repetitions. It has not been re-measured;
the results below must not be attributed to the current reservation policy.

## CMS encoder phases

These diagnostics use the benchmark's inputs and normalization, on the same
Apple M3 Pro / Rust 1.97.1 machine as the October 9 measurements. The profiling
build inherits the bench profile (fat LTO, one codegen unit), adding debug symbols.
Each phase has one second of warmup and three seconds of measurement. Setup and
final output destruction are untimed. Separate phase medians need not add up to
the combined median; these are diagnostics, not Criterion confidence estimates.

Unsampled run: `20261010T173606Z-f31c6a2d`. Sampling run:
`20261010T162125Z-01134bbf`. Raw measurements, machine/source metadata, logs and
sampling call trees are under `target/vest-bench/profiles/`.

| Corpus | Encoder | Preparation / sizing (ms/pass) | Writing (ms/pass) | Combined (ms/pass) |
| --- | --- | ---: | ---: | ---: |
| 1,024 ContentInfo | Vest | 0.010 | 0.050 | 0.060 |
| 1,024 ContentInfo | RustCrypto | 0.003 | 0.042 | 0.043 |
| 1,024 ContentInfo | rasn | Not separately exposed | Not separately exposed | 0.239 |
| 304 SignedData | Vest | 1.429 | 1.750 | 3.227 |
| 304 SignedData | RustCrypto | 0.126 | 1.888 | 1.985 |
| 304 SignedData | rasn | Not separately exposed | Not separately exposed | 8.510 |

`Writing` caches only the top-level output lengths. Both encoders still calculate
nested TLV lengths while writing. Only `Combined` follows the normal benchmark's
sizing/allocation policy. Rasn allocates fresh outputs, retained until timing stops.

### What explains the differences?

- Vest's writing-only SignedData pass is close to RustCrypto's. Its preparation
  takes roughly 44% of the combined time. Plain `length` takes only 0.156 ms;
  preparation also validates values and checks canonical DER SET OF order.
- In the sampled preparation pass, 618 of 846 top-of-stack samples (73%) fall
  in `der_ord` cursor functions. Attribute pair cursors and ANY/OID byte cursors
  dominate. This supports ordering validation, not just size calculation, as the
  main preparation cost. Short sampling runs and inlining limit attribution accuracy.
- RustCrypto's SET OF constructor/mutation APIs sort values, but its writer
  streams the stored order without rechecking. In this benchmark, BER decoding
  preserves the already sorted, normalized serializer inputs; BER decoding does
  not itself establish canonical order. Vest accepts plain vectors and rechecks
  them during preparation. RustCrypto's writing samples show header encoding,
  nested length calculation and copying.
- Vest stores OIDs as arcs, so it validates and base-128-encodes them. RustCrypto's
  OID type stores encoded bytes. OID/base-128 work is visible in Vest's samples,
  particularly for the small ContentInfo workload.
- Rasn repeatedly builds child buffers for constructed values and encodes SET OF
  elements before sorting their encoded ranges. Its samples show copying,
  allocation/growth and temporary-buffer management. The earlier allocation audit
  recorded about 128 MB of cumulative requests per SignedData serialization pass,
  compared with zero for Vest and RustCrypto using reusable destinations.

The sampling profiler also observes untimed final-output destruction. Its entire
call tree must not be interpreted as a breakdown of the timed encoding region.
The phase timer itself excludes that destruction. No signature verification is
performed by any of these codecs.

## Reservation policy

The old Star parser reserved `input_bytes / minimum_encoded_length` elements,
substituting one byte when the hint was zero. That is an upper bound, not a good
estimate of the actual collection size. Generated nominal ASN.1 parsers also
lost the hints supplied by their inner formats.

For one DSS input, a single 832-byte certificate value caused a reservation of
309,417 slots (245.5 MiB). The new reservation is 19 slots.

The measured policy was:

- Star, Repeat and RepeatTillEnd start with at most 32 estimated elements and
  at most 16 KiB of element storage.
- RepeatN knows its element count but still bounds speculative initial storage
  to 16 KiB, also retaining the existing input-length cap.
- Zero-sized elements reserve nothing. Elements larger than the byte budget
  allocate only after a successful parse.
- Successful pushes can grow the vector normally. These are initial-allocation
  limits, not limits on accepted collections or total parser memory.
- Nominal ASN.1 parsers forward their inner minimum-length hint. Specialized BER
  TLV parsers supply a conservative two-octet hint.

The byte cap alone reduced CMS requests from 4.46 GiB to 26.0 MiB, but barely
helped fragmented CBOR: many narrow chunk vectors still reserved large counts.
The additional Star element cap addressed that case in the measured version;
it is not part of the current policy. The trade-off is extra
growth for long collections; cumulative allocation requests can increase even
when initial reservation is safer. The dated benchmark snapshots record both
allocation and reallocation counts, rather than treating fewer reservations as
an unconditional performance improvement.

## Historical full-suite measurements

The final run, `20261010T173855Z-5d84d69f`, includes all 99 timing measurements
and 99 separate allocator audits. It uses the same timing policy as the October 9
run. The [complete snapshot](2026-10-10.md) contains confidence intervals and all
baseline measurements; quick validation runs are not used here.

| Vest parse workload | Requested storage before → after (MiB/pass) | Throughput before → after (MiB/s) |
| --- | ---: | ---: |
| CMS SignedData | 4,562.7 → 20.6 | 4,748.5 → 6,547.6 |
| TLS Certificate | 3.90 → 0.175 | 43,559.9 → 66,177.9 |
| TLS ClientHello | 2.84 → 0.538 | 2,555.1 → 2,973.3 |
| Fragmented CBOR | 7.06 → 2.55 | 496.7 → 525.3 |
| Bitcoin | 7.04 → 9.38 | 5,575.7 → 5,220.9 |
| Tail list microformat | 9.74 → 3.66 | 7,399.4 → 9,575.2 |

CMS requests fall by 221× with 16 additional reallocations (112 → 128).
Bitcoin adds 28 reallocations (0 → 28), raises cumulative requests by 33%, and
loses about 6% parsing throughput in this run. The initial reservation policy is
safer for malformed input, but geometric growth has a cost for large valid
collections with an exact count. Fragmented CBOR still requests more storage
than its owned baselines: reducing reservation does not equalize their value
representations or eliminate all temporary storage.

Serializer implementations were not optimized in this change. CMS SignedData
serialization is 3,179.9 MiB/s (Vest), 5,880.2 (RustCrypto), and 1,377.0 (rasn).
The phase investigation explains the preparation cost; its numbers are not an
exact decomposition of Criterion timings. Before/after throughput differences
also include independent-run variance and code-layout changes from the cleanup.
