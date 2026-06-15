# Benchmark Results Comparison

| Benchmark | Type | handrolled_bulk Time | vest_fixwith_bulk Time | handrolled_bulk Thrpt | vest_fixwith_bulk Thrpt |
| --- | --- | --- | --- | --- | --- |
| mutual_fix_expr | Parse | 14.559 µs | 15.724 µs (0.93x) | 103.76 MiB/s | 96.072 MiB/s (0.93x) |
| mutual_fix_expr | Serialize | 2.2415 µs | 3.5769 µs (0.63x) | 673.93 MiB/s | 422.33 MiB/s (0.63x) |
| mutual_fix_list | Parse | 13.285 µs | 13.925 µs (0.95x) | 106.82 MiB/s | 101.91 MiB/s (0.95x) |
| mutual_fix_list | Serialize | 2.2369 µs | 3.3019 µs (0.68x) | 634.39 MiB/s | 429.77 MiB/s (0.68x) |
| self_fix_byte_list | Parse | 9.6063 µs | 10.341 µs (0.93x) | 133.43 MiB/s | 123.95 MiB/s (0.93x) |
| self_fix_byte_list | Serialize | 1.7295 µs | 1.8672 µs (0.93x) | 741.10 MiB/s | 686.43 MiB/s (0.93x) |

Note: Values in parentheses show the speedup factor relative to 'handrolled_bulk'.
* For Time: baseline time / flavor time (higher is better, >1.0x means faster than baseline).
* For Thrpt: flavor thrpt / baseline thrpt (higher is better, >1.0x means faster than baseline).