# Bitcoin runtime corpus

The full runtime corpus is not bundled because it is an 897 MiB text file. It
contains one base64-encoded Bitcoin block per line and was used identically by
Vest and VPS.

- file name: `sampled_blocks.txt`
- SHA-256: `b60ec4397a73b539b8f6ec358a9584c76ee74150a073baaea40aaa9d5b0e244f`
- decoded bytes measured per benchmark iteration: `705062422`

Place the file at
`vest-dsl-vps/test/bench_data/bitcoin/sampled_blocks.txt`, or set
`VPS_BITCOIN_CORPUS` to its location before running the Vest/VPS Criterion
benchmark. The retained `throughput.tsv` records the exact denominator used to
derive the paper's throughput numbers, so regenerating tables and plots does
not require the corpus.
