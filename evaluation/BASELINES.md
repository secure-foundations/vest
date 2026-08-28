# Runtime baseline selection

This file records the baseline decision before measuring performance. It avoids
selecting or dropping implementations after seeing favorable timing results.

## Inclusion rule

A headline comparison must parse and serialize the same wire-language subset and
materialize an equivalent logical value. Differences in ownership (for example,
VPS borrowing a definite CBOR byte string while a baseline owns it) are reported
because they are part of the API cost, but recognition-only APIs are not compared
against value-producing codecs.

## Candidates

| Domain | Candidate | Pilot decision | Reason / required configuration |
|---|---|---|---|
| Generic CBOR | `ciborium` | Include | Provides a generic `Value` and reader/writer APIs; closest direct comparison to `CborValue`. |
| Generic CBOR | `cbor4ii` | Include via Serde | Deserialize/serialize `ciborium::Value` so both open-source codecs materialize exactly the same value type. |
| Generic CBOR | `minicbor-serde` | Include via Serde | Deserialize/serialize the same `ciborium::Value` used by the other open-source codecs. |
| ASN.1 DER/BER | `rasn` | Include | Supports both BER and DER and generated/derived schema types. Use the same curated record types and corpus. |
| ASN.1 DER/BER | `bcder` | Pilot | Supports BER/CER/DER, but schema codecs are manual. Include only after matching the same value materialization and accepted language. |
| ASN.1 DER/BER | RustCrypto `der` | Include for DER and the common BER parse subset | DER uses borrowed string references. Its optional `ber` feature decodes a deliberately restricted BER subset, so comprehensive BER forms rejected by RustCrypto are reported separately. Encoding remains DER. |
| CMS | `rasn-cms` | Include | Supplies RFC CMS types over rasn’s BER/DER codecs. Compare common `ContentInfo` inputs accepted by both. |
| CMS | `cryptographic-message-syntax` | Include for the ContentInfo microbenchmark | Its bcder-backed `Captured` content representation is close to VPS's raw `Any` representation, but serialization largely copies already encoded content; report this explicitly. |
| CMS | RustCrypto `cms` | Include for DER | DER-oriented typed CMS implementation. Compare the common DER `ContentInfo` subset only. |

## Corpus policy

- Constructed synthetic inputs cover primitive values, nested records, choices,
  repeated values, and large byte/string payloads. BER additionally covers constructed-definite,
  constructed-indefinite, and recursively fragmented OCTET STRINGs, nested indefinite containers,
  non-minimal lengths, and alternative TRUE octets. CBOR covers over-wide integer arguments,
  fragmented byte/text strings, and recursively indefinite arrays/maps.
- The common BER parse table uses exactly the inputs accepted by VPS, rasn, and RustCrypto.
  A separate comprehensive table retains legal BER alternatives rejected by RustCrypto's
  intentionally restricted decoder. BER serialization is normalized definite output.
- VPS and RustCrypto use borrowed string fields for DER. BER fragmented strings necessarily use
  owned reassembly. Generic CBOR rows materialize generic value trees; cbor4ii/minicbor borrowing
  available through specialized targets is outside that experiment.
- Real CMS inputs are retained only if every implementation in a table accepts
  them. Counts and total bytes are reported alongside throughput.
- Real CMS is stratified by provenance rather than pooled: NIST PKITS for ordinary signed S/MIME,
  European Commission DSS for complex CAdES/BER and large objects, and RFC 4134 for authoritative
  interoperability examples. Intentional negative fixtures remain in acceptance statistics but
  are excluded from successful-parse timing.
- Parsing and serialization are separate experiments. Values and exact output
  lengths are prepared before serialization timing; output buffers are reused.
- Every retained input is round-tripped and its logical value or canonical bytes
  checked before Criterion runs.
- Runtime figures use Criterion's median point estimate. Whiskers transform its
  bootstrap standard-deviation point estimate from time to throughput; the
  derived CSV/JSON files retain both values for independent plotting.

In addition to the synthetic coverage corpus, the CBOR evaluation includes 49
complete COSE Sign, Sign1, Encrypt0, MAC, and MAC0 messages from the IETF COSE
Working Group example repository. Parsing materializes the complete generic CBOR
tree and serialization normalizes it; neither operation performs cryptography.
The tagged corpus is compared only with ciborium: the cbor4ii and
minicbor-serde adapters into the common `ciborium::Value` reject the semantic
tags used by 44 of the 49 messages.

The synthetic CMS corpus contains `ContentInfo` values carrying the `id-data`
content type. It exercises the generated full CMS module at its public boundary
but is only a codec/API microbenchmark. The application-level evaluation
separately reports three real `SignedData` strata: 223 official NIST PKITS signed
S/MIME messages, 74 European Commission DSS CAdES fixtures, and seven RFC 4134
interoperability examples. Inputs are neither pooled across sources nor
normalized before parsing; each stratum is the exact three-way BER intersection.
Both the provenance-specific strata and their directly sampled 304-message concatenation are
reported; the combined standard deviation is measured directly by Criterion
rather than propagated from the three strata.
