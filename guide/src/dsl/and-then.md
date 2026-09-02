# `>>=`

`left >>= right` means "take the region `left` describes, then parse `right` against it."

The corresponding Rust value type of the whole expression is the same as `right`'s.

**Parsing.** Extract a bounded region from the input defined by `left`, then parse `right` from that region.
`right` must consume the region *entirely* — leftover bytes
are an error.

**Preparation and serialization.** Preparation prepares `right` and requires its
length to equal the region `left` declares. Serialization writes
`right`'s bytes directly.

Currently, the left side must be `[u8; length]` or `Tail`. We're working on generalizing this to any format that can be reinterpreted within a bounded region.

## Bounding `Vec` with a length field

```vest
item = { value: u16, }

list = {
    @byte_length: u16,
    values: [u8; @byte_length] >>= Vec<item>,
}
```

Here, `Vec<item>` repeats until its region (`[u8; @byte_length]`) runs out. Because the region is exactly
`byte_length` bytes, the repetition will eventually stop. Preparation checks that the items really do add up to `byte_length`.

## Reinterpreting the remainder of a region

`Tail` names everything left in the enclosing region, which turns `>>=` into
"reinterpret the remainder":

```vest
item = { value: u16, }

items = Tail >>= Vec<item>
```

This is the idiom for a message that ends in an unknown number of records. It
also composes: inside a format already bounded by a length field, `Tail` means
the rest of *that* region, not the rest of the original input buffer.
