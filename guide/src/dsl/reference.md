# Vest language reference

## Overview

| Topic                                          | Covers                                                      |
| ---------------------------------------------- | ----------------------------------------------------------- |
| [File structure and lexical rules](lexical.md) | definitions, comments, names, literals, and byte order      |
| [Primitive formats](primitives.md)             | integers, byte strings, `Tail`, `Nothing`, and `Never`      |
| [Refinements](refinements.md)                  | integer and enum constraints                                |
| [Structures and dependencies](structs.md)      | fields, dependencies, constants, and length expressions |
| [Enums](enums.md)                              | closed, open, typed, and bit-sized enums                    |
| [Choices](choices.md)                          | dependent dispatch and ordered alternatives                 |
| [Collections](collections.md)                  | arrays, `Vec`, and `Option`                                 |
| [`>>=`](and-then.md)                           | reinterpretation of a bounded byte region as another format |
| [Bit fields](bits.md)                          | `bits` blocks, bit-sized fields, and bit-level refinements  |
| [Composition](composition.md)                  | format aliases, `wrap`, parameters, and macros              |
| [Recursion](recursion.md)                      | self-recursive formats and mutually recursive formats       |

## How each construct is described

Every format construct is given as what it _means_ on the wire, plus how it
behaves under Vest's three core executable APIs:

- **parse** reads bytes and returns a value together with the number of bytes
  consumed;
- **prepare** checks that a value is _consistent_ with the format (its
  dependencies, constants, and refinement constraints all hold) and returns the exact
  number of bytes it will occupy;
- **serialize** writes a prepared value into a caller-owned buffer of exactly
  that size, without failing or allocating.

The [generated Rust code guide](generated-api.md) explains the Rust
types, format types, executable APIs,
and specs/proofs that the compiler emits for each construct.
The [construct-to-Rust table](mapping.md) provides a quick reference for the DSL constructs and their corresponding Rust types.

## Limitations

- The DSL does not support polymorphic or "higher-kinded" formats that take other _formats_ as parameters.
- The DSL does not support arbitrary _semantic transformations_ or _parsing actions_ on the data.
- The DSL does not support expressing _backward dependencies_ (e.g., a field that depends on a later field like footers).
- The DSL does not have a module/namespace system (so you cannot "import" a format from another `.vest` file).
- The DSL does not support declaring "trusted"/"external" formats that are implemented in Rust/Verus and used in the DSL.
