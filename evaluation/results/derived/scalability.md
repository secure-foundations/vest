# Vest versus VPS scalability

Depth is a chain of single-field records; structure width is the number of `u8` fields in one record; choice width is the number of tag-disjoint `u8` alternatives in one choice. Measurements use a warm shared target cache, 10 workers, a 300 s limit, and Rust recursion limit 512.

| Shape | Size | System | Generated SLOC | VCs | Verus (s) | Rust (s) | Verify wall (s) | Process wall (s) | SMT CPU (s) | Result |
|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---|
| depth | 1 | vest | 381 | 34 | 0.57 | 0.13 | 0.44 | 1.21 | 0.06 | pass |
| depth | 1 | vps | 675 | 44 | 0.65 | 0.13 | 0.51 | 1.33 | 0.07 | pass |
| depth | 4 | vest | 900 | 85 | 0.87 | 0.17 | 0.69 | 1.47 | 0.20 | pass |
| depth | 4 | vps | 1608 | 110 | 0.92 | 0.21 | 0.68 | 1.57 | 0.20 | pass |
| depth | 8 | vest | 1592 | 153 | 1.73 | 0.24 | 1.45 | 2.35 | 0.78 | pass |
| depth | 8 | vps | 2852 | 198 | 1.36 | 0.32 | 1.00 | 2.38 | 0.52 | pass |
| depth | 16 | vest | 2976 | – | – | – | – | 300.01 | – | timeout |
| depth | 16 | vps | 5340 | 374 | 110.44 | 0.56 | 109.79 | 111.23 | 109.03 | pass |
| struct | 1 | vest | 208 | 17 | 0.49 | 0.11 | 0.37 | 1.29 | 0.03 | pass |
| struct | 1 | vps | 364 | 22 | 0.57 | 0.10 | 0.46 | 1.14 | 0.03 | pass |
| struct | 4 | vest | 241 | 26 | 0.59 | 0.10 | 0.47 | 1.33 | 0.09 | pass |
| struct | 4 | vps | 427 | 22 | 0.68 | 0.11 | 0.56 | 1.25 | 0.11 | pass |
| struct | 8 | vest | 285 | 38 | 0.85 | 0.14 | 0.69 | 1.40 | 0.24 | pass |
| struct | 8 | vps | 511 | 22 | 0.84 | 0.12 | 0.71 | 1.50 | 0.26 | pass |
| struct | 16 | vest | 373 | 62 | 5.16 | 0.28 | 4.81 | 5.67 | 0.79 | pass |
| struct | 16 | vps | 679 | 22 | 1.67 | 0.13 | 1.52 | 2.66 | 0.80 | pass |
| choice | 2 | vest | 259 | 22 | 0.57 | 0.12 | 0.44 | 1.23 | 0.06 | pass |
| choice | 2 | vps | 422 | 22 | 0.60 | 0.11 | 0.48 | 1.23 | 0.05 | pass |
| choice | 4 | vest | 327 | 30 | 0.71 | 0.14 | 0.55 | 1.28 | 0.13 | pass |
| choice | 4 | vps | 504 | 22 | 0.64 | 0.11 | 0.51 | 1.20 | 0.09 | pass |
| choice | 8 | vest | 463 | 46 | 1.31 | 0.25 | 1.01 | 1.83 | 0.42 | pass |
| choice | 8 | vps | 668 | 22 | 0.77 | 0.13 | 0.62 | 1.36 | 0.18 | pass |
| choice | 16 | vest | 735 | 78 | 3.86 | 0.77 | 2.93 | 4.47 | 1.50 | pass |
| choice | 16 | vps | 996 | 22 | 1.05 | 0.15 | 0.88 | 1.65 | 0.44 | pass |
| choice | 32 | vest | 1279 | 142 | 25.22 | 4.96 | 19.55 | 25.86 | 10.53 | pass |
| choice | 32 | vps | 1655 | 22 | 1.93 | 0.22 | 1.68 | 2.62 | 1.83 | pass |
| choice | 64 | vest | 2367 | – | – | – | – | 208.90 | – | 101 |
| choice | 64 | vps | 2967 | 22 | 7.91 | 0.35 | 7.51 | 8.56 | 9.81 | pass |
