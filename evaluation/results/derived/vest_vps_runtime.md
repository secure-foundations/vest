# Vest versus VPS runtime

Output buffers and parsed values are prepared outside the timed region.

| Format | Operation | System | Time | MiB/s | Speedup over Vest |
|---|---|---|---:|---:|---:|
| Bitcoin | parse | Vest | 197.26 ± 1.98 ms | 3408.8 | 1.00× |
| Bitcoin | parse | VPS | 180.01 ± 1.87 ms | 3735.3 | 1.10× |
| Bitcoin | serialize | Vest | 153.74 ± 3.59 ms | 4373.6 | 1.00× |
| Bitcoin | serialize | VPS | 82.87 ± 12.42 ms | 8113.7 | 1.86× |
| TLS | parse | Vest | 97.63 ± 1.32 µs | 731.8 | 1.00× |
| TLS | parse | VPS | 89.58 ± 7.27 µs | 797.6 | 1.09× |
| TLS | serialize | Vest | 17.06 ± 0.27 µs | 4188.3 | 1.00× |
| TLS | serialize | VPS | 22.18 ± 0.38 µs | 3221.3 | 0.77× |
