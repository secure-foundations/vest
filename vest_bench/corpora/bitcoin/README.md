# Bitcoin corpus

Four consecutive Bitcoin mainnet blocks, heights 968325 to 968328, mined
between 2026-09-23 22:43 and 23:19 UTC. Together they contain 15,848
transactions in 6,517,345 bytes. Each `<height>.bin` file is a raw serialized
block, as returned by `https://mempool.space/api/block/<hash>/raw`.
`MANIFEST.tsv` records each block's height, hash, and size.

The blocks are authentic, which the corpus tests check with rust-bitcoin:
each header hashes to the block hash in the manifest, the transactions match
the header's Merkle root, and the witness data matches the coinbase's witness
commitment.

## Validation

`cargo test -p vest_bench --test real_corpora` checks that the Vest
specification in [`vest_tests/src/bitcoin.vest`](../../../vest_tests/src/bitcoin.vest)
accepts each block, consumes all of its bytes, and re-serializes to the same
bytes. It also checks that Vest agrees with rust-bitcoin on every
transaction's input, output, and witness-stack counts, and on which
transactions use the SegWit serialization.

To benchmark a larger corpus instead, see the
[`vest_bench` README](../../README.md).
