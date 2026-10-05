# Benchmarks

The [`vest_bench`](https://github.com/secure-foundations/vest/tree/main/vest_bench)
crate contains Vest's maintained runtime benchmark suite. It covers both the
cost of Vest's abstractions and complete real-world formats.

The focused benchmarks compare eight generated codecs with hand-written Rust
for exactly the same wire format and value layout. The real-format benchmarks
compare Vest's TLS, Bitcoin, CMS, and CBOR codecs with established Rust
libraries. Those comparisons use each library's natural Rust types; requiring
identical internal layouts would measure an artificial constraint rather than
normal use of each API.

The checked-in real-data corpora include TLS 1.3 handshakes captured from
public servers and Chrome, recent Bitcoin mainnet blocks, CMS `SignedData`
messages from NIST PKITS, European Commission DSS CAdES, and RFC 4134, and
CBOR messages from the IETF COSE Working Group. Corpus provenance, licenses,
and selection rules are stored alongside the data. Because the TLS and Bitcoin
corpora are real traffic, the suite's tests also use them to check that the
Vest specifications accept, and exactly re-serialize, what deployed
implementations send.

To compile every benchmark and execute its validation path once:

```console
make -C vest_bench smoke
```

To collect Criterion measurements:

```console
make -C vest_bench bench
```

To summarize measurements already collected, without rerunning them:

```console
make -C vest_bench report
```

The text report includes confidence intervals, Vest-relative ratios, and MiB/s
for byte-oriented workloads. Criterion's interactive report is written to
`target/criterion/report/index.html`.

See the [`vest_bench` README](https://github.com/secure-foundations/vest/blob/main/vest_bench/README.md)
for individual targets, fairness rules, and how to benchmark a larger Bitcoin corpus.
