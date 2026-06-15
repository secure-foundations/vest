# Benchmark Results Comparison

| Benchmark | Type | A_handrolled Time | B_tagged Time | C_vest_fixwith Time | A_handrolled Thrpt | B_tagged Thrpt | C_vest_fixwith Thrpt |
| --- | --- | --- | --- | --- | --- | --- | --- |
| tree | Parse | 69.331 µs | 80.909 µs (0.86x) | 92.441 µs (0.75x) | 165.06 MiB/s | 141.44 MiB/s (0.86x) | 123.80 MiB/s (0.75x) |
| tree | Prepare | 13.265 µs | 20.337 µs (0.65x) | 19.626 µs (0.68x) | N/A | N/A | N/A |
| tree | Serialize | 14.093 µs | 25.605 µs (0.55x) | 21.559 µs (0.65x) | 812.01 MiB/s | 446.95 MiB/s (0.55x) | 530.84 MiB/s (0.65x) |

Note: Values in parentheses show the speedup factor relative to 'A_handrolled'.
* For Time: baseline time / flavor time (higher is better, >1.0x means faster than baseline).
* For Thrpt: flavor thrpt / baseline thrpt (higher is better, >1.0x means faster than baseline).