# Vest benchmarks

`vest_bench` measures the throughput of Vest-generated parsers and serializers using [Criterion](https://crates.io/crates/criterion).
It provides two benchmark families:

- focused microformats compare Vest-generated codecs with hand-written Rust implementations that have the same value layout and wire behavior, and
- real formats compare Vest-generated codecs with existing unverified Rust libraries for TLS, Bitcoin, CMS, and CBOR.

Benchmark setup and corpus construction happen outside Criterion's timed loop. Every target validates its corpus before measuring it and reuses serialization buffers. Real formats report byte throughput; microformats report element throughput and latency.

## Benchmarks

| Target | Workload | Comparison |
| --- | --- | --- |
| `formats` | Eight small formats isolating structs, repetition, nesting, TLV, varints, bits, bounded lists, and tail lists | Hand-written Rust with the same value layout and wire behavior |
| `tls` | 909 TLS 1.3 handshake messages captured from 16 public servers and Chrome, one group per message type | [Rustls 0.22](https://crates.io/crates/rustls/0.22.4)'s publicly exposed low-level (`internal`) message codec |
| `bitcoin` | Four consecutive mainnet blocks (15,848 transactions), or an external block corpus | [`bitcoin`](https://crates.io/crates/bitcoin)'s consensus codec |
| `cms` | Synthetic `ContentInfo` plus 304 real `SignedData` messages | `rasn-cms`, RustCrypto `cms`, and, for `ContentInfo`, `cryptographic-message-syntax` |
| `cbor` | Synthetic fragmented and definite CBOR, plus 49 IETF COSE vectors | `ciborium`, `cbor4ii`, and `minicbor-serde` where their generic value models and consumption checks support the corpus |

The TLS corpus was captured from live TLS 1.3 connections, and the Bitcoin
corpus holds recent mainnet blocks. The CMS corpus combines NIST PKITS,
European Commission DSS CAdES, and RFC 4134. The CBOR corpus comes from the
IETF COSE Working Group. Their provenance, manifests, licenses, and selection
rules are under [`corpora/`](corpora/).

The TLS and Bitcoin corpora also validate the Vest specifications against
deployed implementations: `cargo test --test real_corpora` requires every
captured message, record, and block to parse, consume all of its bytes, and
re-serialize to the same bytes, and cross-checks the blocks with rust-bitcoin.

To benchmark a larger Bitcoin corpus, set `VEST_BENCH_BITCOIN_CORPUS` to a
text file containing one base64-encoded block per line:

```console
VEST_BENCH_BITCOIN_CORPUS=/path/to/sampled_blocks.txt \
  cargo bench -p vest_bench --bench bitcoin
```

## Running

From this directory:

```console
make generate       # regenerate microformat modules from formats/*.vest
make test           # layout parity, wire compatibility, and real-corpus validation
make smoke          # compile all benchmarks and execute each setup once
make bench          # run every benchmark
make bench-formats  # only Vest-versus-hand-written microformats
make bench-real     # only TLS, Bitcoin, CMS, and CBOR
make report         # summarize all stored Criterion measurements
```

Individual targets can also be run directly:

```console
cargo bench -p vest_bench --bench tls
cargo bench -p vest_bench --bench bitcoin
cargo bench -p vest_bench --bench cms
cargo bench -p vest_bench --bench cbor
```

The microbenchmarks run one process per format because their measurements are
allocation-sensitive. Override `FORMATS` to select a subset:

```console
make bench-formats FORMATS="bounded_list tail_list"
make report TARGETS="bounded_list tail_list"
```

`make report` does not rerun benchmarks. It reads Criterion's stored estimates
and prints confidence intervals, Vest-relative ratios, and byte throughput for
the real formats. Pass `TARGETS="tls cms"`, for example, to select benchmark
families. Criterion's complete interactive report is available at
`../target/criterion/report/index.html` after measurement runs.

## Fairness rules

For microformats, `layout_parity` checks identical Rust size and alignment,
while `wire_compat` checks identical bytes, cross-parser acceptance, and the
same validation behavior. Both sides expose their result to `black_box`.

For real formats, forcing identical internal layouts would penalize libraries
for ordinary API-design choices. Instead, every implementation parses the same
bytes into its native type and serializes equivalent values. Input construction,
parsing used to prepare serializer inputs, and output allocation are excluded
from the timed loop. Each serializer reuses one buffer sized for its largest
message, rather than keeping a buffer per message.

Two baseline limitations:

- `cryptographic-message-syntax` 0.28.0 omits the `ContentInfo` `[0] EXPLICIT`
  wrapper when encoding. The benchmark builds the correct wrapper with public
  bcder combinators, including that work in the timed loop. Issue filed: https://github.com/indygreg/cryptography-rs/issues/99
- `cbor4ii` 1.2.3 leaves indefinite-string break bytes unread. It is excluded
  from fragmented-input parsing, but included in the separate `synthetic_definite`
  comparison and in serialization, where the output checks pass. Issue filed: https://github.com/quininer/cbor4ii/issues/60
