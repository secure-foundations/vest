# VPS backend source and proof burden

Ratios use nonblank, non-comment SLOC. Shared declarations are apportioned
evenly among Spec, Proof, and Impl (with at most one rounding line per column),
so these three columns sum to SLOC. P/C = (Spec + Proof) / Impl.

| Area | Modules | SLOC | Spec | Proof | Impl | Raw shared | P/C Ratio | Formats |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| core | 12 | 2700 | 715 | 1286 | 699 | 706 | 2.86 | 0 |
| combinators | 79 | 21396 | 7334 | 9980 | 4082 | 6473 | 4.24 | 15 |
| primitives | 5 | 1718 | 422 | 824 | 472 | 331 | 2.64 | 3 |
| asn1 | 35 | 17912 | 5632 | 5480 | 6800 | 5333 | 1.63 | 136 |
| cbor | 5 | 3185 | 1038 | 917 | 1230 | 1044 | 1.59 | 16 |
| library_root | 2 | 232 | 101 | 66 | 65 | 197 | 2.57 | 0 |
| FRAMEWORK | 96 | 25814 | 8470 | 12090 | 5254 | 7510 | 3.91 | 18 |
| CASE_STUDIES | 40 | 21097 | 6670 | 6397 | 8030 | 6377 | 1.63 | 152 |
| TOTAL | 138 | 47143 | 15240 | 18553 | 13350 | 14084 | 2.53 | 170 |
