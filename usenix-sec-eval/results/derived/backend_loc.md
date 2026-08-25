# VPS backend source and proof burden

Ratios use nonblank, non-comment SLOC. P/C = (Spec + Proof) / Exec.

| Area | Modules | SLOC | Spec | Proof | Exec | Shared | P/C Ratio | Formats |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| core | 12 | 2700 | 479 | 1051 | 464 | 706 | 3.30 | 0 |
| combinators | 79 | 21396 | 5176 | 7822 | 1925 | 6473 | 6.75 | 15 |
| primitives | 5 | 1718 | 311 | 714 | 362 | 331 | 2.83 | 3 |
| asn1 | 35 | 17912 | 3854 | 3702 | 5023 | 5333 | 1.50 | 136 |
| cbor | 5 | 3185 | 690 | 569 | 882 | 1044 | 1.43 | 16 |
| library_root | 2 | 232 | 35 | 0 | 0 | 197 | – | 0 |
| TOTAL | 138 | 47143 | 10545 | 13858 | 8656 | 14084 | 2.82 | 170 |
