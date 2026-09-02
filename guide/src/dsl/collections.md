# Collections

## Fixed and dependency-sized arrays

A repetition of one format a known number of times.

```vest
fixed_words = [u16; 8]

counted = {
    @count: u16,
    words: [u32; @count],
}
```

A constant count generates a Rust array. A dependency-sized repetition
generates a `Vec`, because its length is known only at runtime. `[u8; length]` is
specialized to a borrowed byte slice.

**Parsing.** Parses the element format exactly `count` times, one after another.

**Preparation and serialization.** Preparation checks that the collection holds
exactly `count` elements, prepares each element, and sums the lengths.
Serialization writes the elements back to back.

Nested arrays are supported:

```vest
matrix = {
    @rows: u16,
    @columns: u16,
    cells: [[u8; @columns]; @rows],
}
```

## `Vec`

A repetition with no count: zero or more occurrences of a format. The result is a `Vec` in Rust.

```vest
item = { value: u16, }

items = Vec<item>
```

**Parsing.** Repeats the element format until it errors (e.g., the input is exhausted).

**Preparation and serialization.** Preparation prepares every element and sums
the lengths. Serialization writes the elements in order.

Because there is no count, the element must be *productive* — every successful
element parse must consume at least one byte. Otherwise repetition could loop
forever. Verus will check this property in the emitted Rust code and reject the format if productivity cannot be proven for the element format.

## `Option`

Zero or one occurrence of a format.

```vest
tagged = wrap(u8 = 1, u16)
maybe_tagged = Option<tagged>
```

**Parsing.** Tries the inner format. On success the result is `Some(v)`; on
failure the result is `None` and **no input is consumed**, so parsing continues
from the same position.

**Preparation and serialization.** `Some(v)` prepares and writes the inner
format; `None` has length 0 and writes nothing.

## Notes on `Vec` and `Option`

Because a `Vec` can be empty and an `Option` can be absent, the surrounding format must make their presence
distinguishable from what follows — a tagged or otherwise disjoint inner format is the usual pattern.
A chain of ambiguous `Vec` or `Option` fields will fail the generated unambiguity proof obligations.
