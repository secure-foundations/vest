# Choices

A choice is a format that can take one of several shapes. It generates a Rust
enum, so the alternative that matched is recorded in the value. Vest has *dependent* choices, where an earlier field selects the
branch, and *non-dependent* choices, where branches are tried in order.

## Enum-dependent choices

```vest
kind = enum {
    Short = 1,
    Long = 2,
}

body(@kind: kind) = choose(@kind) {
    Short => u16,
    Long => u64,
}
```

**Parsing.** The dependency has already been parsed, so the branch is chosen
directly — no backtracking, and no ambiguity about which arm applies.

**Preparation and serialization.** Preparation checks that the variant in your
value matches the branch the dependency selects; a `Long` body under a `Short`
tag is rejected before any bytes are written. It then prepares that branch.
Serialization writes the selected branch only.

A closed enum choice must cover every declared variant unless it has a final
wildcard. An open enum choice requires a final `_` branch. Branch names must be
unique and belong to the enum.

## Integer-dependent choices

```vest
body(@kind: u8) = choose(@kind) {
    1 => u16,
    2..10 => u32,
    _ => Never("unknown body kind"),
}
```

Integer patterns use the same values and ranges as refinements. Explicit
patterns must not overlap, and a final wildcard is mandatory because the
integer domain is otherwise open. Semantics are as above: the dependency picks
the arm, and the value must match that arm.

## Byte-string-dependent choices

```vest
record = {
    @magic: [u8; 2],
    body: choose(@magic) {
        [0x01, 0x02] => u16,
        [0x03, 0x04] => u32,
        _ => Nothing,
    },
}
```

Every explicit byte pattern must have the same length as the dependency, and a
final wildcard is required.

## Non-dependent ordered choices

Without `(@dependency)`, there is no tag to dispatch on, so the branches are
distinguished by their own content:

```vest
small = choose {
    Tiny(u8 | 0..9),
    Medium(u8 | 10..100),
}

// or equivalently
small_arrow = choose {
    Tiny => u8 | 0..9,
    Medium => u8 | 10..100,
}
```

**Parsing.** Branches are attempted in source order and the first success wins.
A failed attempt consumes nothing, so the next branch starts from the same
position.

**Preparation and serialization.** Preparation prepares whichever branch the
value holds; serialization writes it.

Note that for non-dependent choices, the variant names (`Tiny` and `Medium`) are **not** part of the wire. In this case, Vest requires that the branches are **non-overlapping**, which is required for the parser to be able to unambiguously select the correct branch.

## Wildcard rules

- `_` may appear at most once and must be the final branch.
- Integer and byte-string choices require it.
- Open-enum choices require it.
- A closed-enum choice is normally written exhaustively, but a final `_` is allowed to "catch all" other variants.
