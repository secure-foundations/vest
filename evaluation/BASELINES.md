# Runtime comparisons

The paper compares only implementations that consume the same bytes and build
comparable values.

| Workload | Implementations |
|---|---|
| TLS and Bitcoin | VPS and original Vest |
| ASN.1 DER | VPS, rasn, and RustCrypto `der` |
| ASN.1 BER parsing | VPS, rasn, and RustCrypto's restricted BER mode |
| CMS | VPS, rasn-cms, RustCrypto `cms`, and cryptographic-message-syntax where comparable |
| Generic CBOR | VPS, ciborium, cbor4ii, and minicbor-serde |

Every comparison uses the same retained input bytes. Correctness is checked
before timing; setup and allocation are excluded when the API allows it; output
buffers are reused. Throughput uses bytes actually read or written because BER
and CBOR serialization may normalize a longer input.

The synthetic inputs include non-canonical and fragmented forms. Real CMS
comes from NIST PKITS, European Commission DSS, and RFC 4134. Real CBOR uses
IETF COSE examples. A timed real-data group contains only files accepted by
every implementation shown in that group.

Exact versions, licenses, hashes, byte counts, and acceptance counts are under
[`corpora/`](corpora/); raw Criterion output is under
[`results/raw/`](results/raw/).
