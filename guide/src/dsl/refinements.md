# Refinements

A refinement narrows an existing format to a subset of its values. The wire
encoding and the Rust type are unchanged — only the set of *accepted* values
shrinks. Writing `u16 | 1..1024` still parses two bytes into a `u16`; it just
refuses the ones outside the range.

**Parsing.** Parses the underlying format, then tests the predicate. A value
outside the refinement is a parse error.

**Preparation and serialization.** Preparation tests the same predicate on the
value you supply and fails if it does not hold. Length and
serialization are those of the underlying format.

The predicate is therefore enforced in both directions.

## Integer constraints

```vest
constrained = {
    exact: u8 | 7,
    range: u16 | 1..1024,
    lower_bounded: u32 | 1..,
    upper_bounded: u16 | ..4096,
    selected: u8 | {1, 4, 9},
    except: u8 | !{0, 255},
}
```

Vest ranges include both supplied endpoints:
`1..1024` accepts 1 through 1024. Either endpoint may be omitted. A set uses
braces and commas; prefixing a
constraint with `!` takes its complement. Values and range endpoints must fit
the underlying integer type.

## Enum constraints

Named enum formats can be restricted by variant:

```vest
kind = enum {
    Request = 1,
    Response = 2,
    Error = 3,
}

messages = {
    request: kind | Request,
    not_error: kind | !Error,
    terminal: kind | {Response, Error},
}
```

Every named variant must belong to the referenced enum. The generated field
still has type `Kind`; the refinement changes only which values are consistent.
