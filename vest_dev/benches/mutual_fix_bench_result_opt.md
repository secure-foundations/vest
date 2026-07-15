# Benchmark Results Comparison

| Benchmark       | Type      | handrolled_bulk Time | vest_fixwith_bulk Time | handrolled_bulk Thrpt | vest_fixwith_bulk Thrpt |
| --------------- | --------- | -------------------- | ---------------------- | --------------------- | ----------------------- |
| mutual_fix_expr | Parse     | 14.608 µs            | 14.640 µs (1.00x)      | 103.41 MiB/s          | 103.19 MiB/s (1.00x)    |
| mutual_fix_expr | Serialize | 2.2304 µs            | 2.1495 µs (1.04x)      | 677.29 MiB/s          | 702.79 MiB/s (1.04x)    |
| mutual_fix_list | Parse     | 13.033 µs            | 13.324 µs (0.98x)      | 108.88 MiB/s          | 106.51 MiB/s (0.98x)    |
| mutual_fix_list | Serialize | 2.2536 µs            | 2.1064 µs (1.07x)      | 629.68 MiB/s          | 673.69 MiB/s (1.07x)    |

Note: Values in parentheses show the speedup factor relative to 'handrolled_bulk'.

- For Time: baseline time / flavor time (higher is better, >1.0x means faster than baseline).
- For Thrpt: flavor thrpt / baseline thrpt (higher is better, >1.0x means faster than baseline).
