# `vest_bench`

Measures what Vest's abstraction costs, by comparing generated codecs against
hand-written ones for the same wire format.

Each schema in `formats/` isolates one construct that appears in real formats.
For every format there is also a hand-written baseline in `src/hand.rs` and a pair of driver loops in
`src/runners.rs`.

## Formats

| Format | Description |
| --- | --- |
| `flat` | A plain struct: fixed-width ints, a fixed byte array, one length-prefixed tail. The per-field baseline. |
| `table` | `[entry; @count]` — counted repetition, and building a `Vec` of borrowed elements. |
| `nest` | Eight header/footer layers around one payload. |
| `tlv` | `[u8; @len] >>= choose(@tag)` — a tagged union inside a length-delimited region. |
| `varint` | `btc_varint` driving both a count and per-item lengths. |
| `bits` | A bit-packed header followed by a byte-aligned body. |
| `bounded_list` | `[u8; @len] >>= Vec<item>` — the dominant shape in real protocols (TLS extension lists). The element count is not known up front. |
| `tail_list` | `Tail >>= Vec<item>` — the same repetition driven off the end of the region. |

## Fair comparison

**Same output type.** Each hand-written value type mirrors the generated one
field for field. `cargo test` checks that the two have the same size and
alignment (`layout_parity`), so neither side is building a cheaper structure
than the other.

**Same bytes.** `wire_compat` checks, for every value in the corpus, that the
generated encoder and the hand-written encoder agree byte for byte and that each
parser accepts the other's output.

**Same validation.** The baselines check what the generated code checks — every
length against the remaining input, every tag against its domain, and a
length-delimited body consumed exactly. On the serialization side `prepare` is
*fallible*: it validates the value against the format before returning a length,
so the `size_*` baselines return `Option<usize>` and perform the same checks.

**Same observation.** Both sides hand their result to `black_box`.

The baselines are meant to be the best a competent engineer would write.

## Running

```sh
make generate   # regenerate src/*.rs from formats/*.vest
make test       # layout parity + wire compatibility
make bench      # measure, then print the table
```

To measure a subset, override `FORMATS`:

```sh
make bench FORMATS="bounded_list tail_list"
make report FORMATS="bounded_list tail_list"   # reprint without re-measuring
```

Criterion's own filter (`cargo bench --bench formats -- 'bounded_list|tail_list'`)
also works, but it runs the whole subset in one process, which is what the note
below warns about. Prefer `FORMATS`.

`make bench` runs **one process per format**. 
These benchmarks are allocation-sensitive, and measuring everything in a single
process is not reproducible: allocator churn from earlier groups inflates later
ones. When this was first measured, `bounded_list/parse` read 660us run together
and ~350us run on its own. Do not compare numbers from a bare `cargo bench`.
