# Generic CBOR runtime

Common corpus: 1536 values, 108864 encoded bytes. It includes over-wide integers, fragmented byte/text strings, and recursively indefinite arrays/maps; serialization normalizes the logical values.

| Operation | Implementation | Time | MiB/s | Throughput relative to VPS |
|---|---|---:|---:|---:|
| parse | VPS | 252.59 ± 3.54 µs | 411.0 | 1.00× |
| parse | ciborium | 637.65 ± 29.38 µs | 162.8 | 0.40× |
| parse | cbor4ii | 239.37 ± 7.80 µs | 433.7 | 1.06× |
| parse | minicbor-serde | 276.02 ± 10.34 µs | 376.1 | 0.92× |
| serialize | VPS | 66.86 ± 5.11 µs | 894.8 | 1.00× |
| serialize | ciborium | 86.16 ± 2.59 µs | 694.3 | 0.78× |
| serialize | cbor4ii | 61.09 ± 3.17 µs | 979.3 | 1.09× |
| serialize | minicbor-serde | 52.40 ± 1.28 µs | 1141.6 | 1.28× |

## COSE Working Group protocol corpus

49 complete COSE messages, 3,997 encoded bytes. cbor4ii and minicbor-serde are omitted because their Serde-to-`ciborium::Value` path rejects semantic tags used by 44 messages.

| Operation | Implementation | Time | MiB/s | Throughput relative to VPS |
|---|---|---:|---:|---:|
| parse | VPS | 8.94 ± 0.13 µs | 426.5 | 1.00× |
| parse | ciborium | 24.71 ± 0.37 µs | 154.3 | 0.36× |
| serialize | VPS | 2.76 ± 0.04 µs | 1381.1 | 1.00× |
| serialize | ciborium | 3.92 ± 0.07 µs | 971.2 | 0.70× |
