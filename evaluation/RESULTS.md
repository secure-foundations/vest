# Headline results

Exact tables are under [`results/derived/`](results/derived/) and raw
measurements under [`results/raw/`](results/raw/).

## Proof effort

The public source contains 25,813 nonblank, non-comment lines in the reusable
VPS framework: 8,469 specification, 12,090 proof, and 5,254 implementation
lines, across 96 modules. Its proof-to-code ratio is 3.91. ASN.1 and CBOR
contain another 21,097 lines, with a ratio of 1.63.

The submitted measurement reports 25,814 framework lines and 3,184
verification conditions in 37.59 seconds. Its source snapshot accidentally
included the declaration and proof run for an unused experimental module while
omitting that module's body from the line counter. The module is not part of
the paper and has been removed here. The current source verifies 3,175
conditions; the submitted timing logs remain unchanged under `results/raw/`.

## VPS versus Vest

VPS verifies Bitcoin in 6.39 seconds versus Vest's 8.32 seconds, and TLS in
53.10 seconds versus 151.00 seconds. VPS parsing is 1.10 times faster on
Bitcoin and 1.09 times faster on TLS. Serialization is 1.86 times faster on
Bitcoin and 0.77 times Vest's speed on TLS.

At choice width 64, VPS verifies in 7.51 seconds while Vest fails. At nesting
depth 16, VPS verifies in 109.79 seconds while Vest times out after 300
seconds.

## ASN.1, CMS, and CBOR

On ASN.1 DER, VPS parses 1.13 times and serializes 1.55 times faster than the
best comparison library. On complex BER, VPS parsing is within 7--9% of rasn.

On 304 real CMS messages, VPS parses at 4,461 MiB/s, 1.59 times RustCrypto and
1.64 times rasn. It serializes at 5,961 MiB/s, matching RustCrypto and reaching
4.54 times rasn's throughput.

On synthetic CBOR, VPS is within 6% of cbor4ii's parsing throughput. On 49
IETF COSE messages, VPS parses 2.76 times and serializes 1.42 times as fast as
ciborium.

See [`verification.md`](results/derived/verification.md),
[`vest_vps_runtime.md`](results/derived/vest_vps_runtime.md),
[`asn1_cms_runtime.md`](results/derived/asn1_cms_runtime.md), and
[`cbor_runtime.md`](results/derived/cbor_runtime.md) for complete numbers.
