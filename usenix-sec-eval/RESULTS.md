# Evaluation snapshot

This file consolidates the current measurements. The machine-readable inputs
and per-run logs remain under `results/raw`; all numbers below are regenerated
by `make stats`.

## Verified backend and proof burden

The VPS backend comprises 47,143 nonblank, non-comment SLOC in 138 modules:
10,545 specification lines, 13,858 proof lines, 8,656 executable lines, and
14,084 shared declaration lines. This gives a reproducible lexical proof/code
ratio of 2.82 ($(\text{Spec} + \text{Proof}) / \text{Exec} = (10{,}545 + 13{,}858) / 8{,}656$).
The backend contains 170 counted format definitions and verifies 3,184 VCs with no errors in 37.59 s wall time on the
recorded host.

These are lexical—not semantic—LOC categories. The complete category and
subsystem breakdowns are in `results/derived/backend_loc.md` and
`results/derived/backend_module_times.md`.

## VPS versus Vest

After synchronizing both systems to the same vstd release, VPS verifies the
Bitcoin fixture in 6.39 s verification wall time versus Vest's 8.32 s, and the
TLS fixture in 53.10 s versus Vest's 151.00 s. These VPS measurements use
isolated one-module crates; the earlier aggregate-crate measurements were
discarded because Rust still type-checked unrelated fixtures. On the common runtime corpora,
VPS parsing is 1.10x Vest for Bitcoin and 1.09x for TLS. With the verified
bulk-copy implementation for slice output, VPS serialization is 1.86x Vest for
Bitcoin and 0.77x Vest for TLS. The exact VCs, Rust/type-checking time, CPU
time, byte counts, and throughput appear in `results/derived/verification.md`
and `results/derived/vest_vps_runtime.md`.

The scalability experiment separates nesting depth, structure width, and
choice width. VPS keeps a constant 22 VCs as structure width grows to 16 and
choice width grows to 64. At choice width 64 VPS verifies in 7.51 s while Vest
fails; at depth 16 VPS verifies but takes 109.79 s while Vest times out at 300 s.
Thus nominal sealing addresses width particularly well, but depth 16 still has
a substantial SMT cliff and must not be presented as constant-cost nesting.

## ASN.1, CMS, and CBOR runtime

The typed ASN.1 benchmark uses 1,024 records. DER uses borrowed string fields in
VPS and RustCrypto. A common BER corpus compares VPS, rasn, and RustCrypto's
restricted BER decoder; a broader corpus adds constructed-definite, recursively
fragmented, and character strings, non-minimal lengths, alternative TRUE octets,
and nested indefinite containers for VPS and rasn. Rasn parses these BER corpora
about 1.07--1.09x as fast as VPS, while VPS normalized serialization is 3.16x
rasn. The normalized serialization denominator is 183,774 bytes rather than the
187,285-byte comprehensive BER input. See `results/derived/asn1_cms_runtime.md`.

The generic CBOR benchmark uses 1,536 values encoded with over-wide integers,
fragmented byte/text strings, and recursively indefinite arrays/maps. Cbor4ii
parses 1.06x as fast as VPS; VPS remains 2.52x ciborium and 1.09x
minicbor-serde. Cbor4ii and minicbor-serde serialize 1.09x and 1.28x as fast as
VPS. Parse throughput uses the 108,864-byte input corpus, while normalized
serialization uses Criterion's 62,726-byte output denominator. The benchmark materializes generic values; fragmented strings necessarily
allocate, while specialized borrowed APIs are outside this comparison.

All generated runtime figures include error bars derived from Criterion's
reported timing dispersion, and tables report the same values as `estimate ±
dispersion`.

The CMS evaluation contains both 1,024 synthetic DER `ContentInfo(id-data)`
values and three real `SignedData` strata: 223 official NIST PKITS signed S/MIME
messages (954,515 bytes), 74 European Commission DSS CAdES fixtures (11,400,481
bytes), and seven RFC 4134 interoperability examples (8,332 bytes). Each stratum
is the exact BER input intersection accepted by VPS, rasn-cms, and
RustCrypto-cms; inputs are not normalized before parsing. Serialization measures
each implementation's normalized output rather than byte-for-byte reproduction
of the possibly malleable BER input. Neither workload performs cryptography.

On PKITS, VPS parses in 1.576 ± 0.045 ms, versus 2.162 ± 0.563 ms for rasn and
2.038 ± 0.030 ms for RustCrypto; serialization takes 0.992 ± 0.017 ms, versus
4.534 ± 0.118 ms and 0.964 ± 0.021 ms. On the much larger DSS corpus, VPS parses
in 1.037 ± 0.015 ms, versus 2.159 ± 0.035 ms and 2.141 ± 0.039 ms, and serializes
in 0.980 ± 0.017 ms, versus 4.772 ± 0.112 ms and 1.044 ± 0.032 ms. On RFC 4134,
the respective parse times are 15.42 ± 0.72, 19.43 ± 0.62, and 19.82 ± 0.19 µs;
serialization takes 9.23 ± 0.12, 38.70 ± 0.56, and 8.28 ± 0.70 µs.

A directly sampled combined group traverses all 304 messages and 12,363,328
bytes per iteration. VPS parses it in 2.643 ± 0.031 ms, versus 4.337 ± 0.052 ms
for rasn and 4.204 ± 0.068 ms for RustCrypto, corresponding to 4,461, 2,718,
and 2,804 MiB/s. Serialization takes 1.978 ± 0.045 ms for VPS, 8.972 ± 0.212 ms
for rasn, and 1.975 ± 0.064 ms for RustCrypto, corresponding to 5,961, 1,314,
and 5,969 MiB/s. Serialization uses the 12,362,531-byte normalized-output
denominator recorded by Criterion, rather than the 12,363,328 input bytes.

PKITS is correctly treated as BER rather than DER: VPS's strict DER parser
accepts only 133 of the 224 upstream messages because 91 use non-canonical
`CertificateSet` ordering, while the corrected mixed-rule BER codec accepts all
224. RustCrypto rejects one other message, leaving 223 timed common inputs.

The real-CBOR supplement contains 49 complete Sign, Sign1, Encrypt0, MAC, and
MAC0 messages from the IETF COSE Working Group interoperability examples. VPS
parses the 3,997-byte corpus in 8.94 µs and serializes its normalized values in
2.76 µs. The corresponding ciborium times are 24.71 µs and 3.92 µs. cbor4ii and
minicbor-serde are omitted from this table because their adapters to the common
generic value reject the semantic tags used by most messages.

## Readiness

Publication-ready after independent reruns and confidence reporting:

- backend LOC/proof burden and verification breakdown;
- matched Vest/VPS verification and runtime methodology;
- width scalability;
- typed ASN.1 and generic CBOR microbenchmarks, with ownership caveats.

Still requiring follow-up:

- repeat all runtime and verification measurements on a quiet, fixed-power host
  and report medians/dispersion across independent runs;
- investigate or explicitly characterize the depth-16 verification cliff;
- record final clean revisions and corpus hashes for the artifact snapshot.
