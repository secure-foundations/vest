# Vest language reference

## Overview

| Topic | Covers |
|---|---|
| [File structure and lexical rules](lexical.md) | definitions, comments, names, literals, and byte order |
| [Primitive formats](primitives.md) | integers, byte strings, `Tail`, `Nothing`, and `Never` |
| [Refinements](refinements.md) | integer and enum constraints |
| [Structures and dependencies](structs.md) | fields, `@` references, constants, and length expressions |
| [Enums](enums.md) | closed, open, typed, and bit-sized enums |
| [Choices](choices.md) | dependent dispatch and ordered alternatives |
| [Collections](collections.md) | arrays, `Vec`, and `Option` |
| [`>>=`](and-then.md) | re-reading a bounded byte region as another format |
| [Bit fields](bits.md) | packed fields, widths, and dotted dependencies |
| [Composition](composition.md) | aliases, `wrap`, parameters, and macros |
| [Recursion](recursion.md) | self-referential and mutually recursive definitions |

## How each construct is described

Every construct below is given as what it *means* on the wire, plus how it
behaves under Vest's three operations:

- **parse** reads bytes and returns a value together with the number of bytes
  consumed;
- **prepare** checks that a value is *consistent* with the format — that its
  dependencies, constants, and refinements all hold — and returns the exact
  number of bytes it will occupy;
- **serialize** writes a prepared value into a caller-owned buffer of exactly
  that size, and cannot fail.

`prepare` is the only fallible half of writing, so each construct's preparation
rules are precisely the conditions a value must satisfy before it can be
serialized.

The [construct-to-Rust table](mapping.md) is a compact lookup when you already
know the format constructs. The [generated Rust code guide](generated-api.md) explains the Rust
types, format types, executable APIs,
and specs/proofs that the compiler emits for each construct.

## Limitations

* The DSL does not support polymorphic or "higher-kinded" formats that take other *formats* as parameters.
* The DSL does not support arbitrary *semantic transformations* or *parsing actions* on the data.
* The DSL does not support expressing *backward dependencies* (e.g., a field that depends on a later field like footers).
* The DSL does not have a module/namespace system (so you cannot "import" a format from another `.vest` file).
* The DSL does not support declaring "trusted"/"external" formats that are implemented in Rust/Verus and used in the DSL.
