# Using `vest_lib`

Most applications should use the Vest DSL or ASN.1 frontend. Use `vest_lib`
directly when the format is easier to express as a reusable Verus combinator or
when implementing a new backend primitive.

A format typically combines:

- primitive byte and integer formats;
- sequencing with `Pair`, `Preceded`, or `Terminated`;
- alternatives with `Choice` or deliberately malleable `Alt`;
- repetition with `Array`, `RepeatN`, `Star`, or `RepeatTillEnd`;
- semantic transformations with `Mapped`, `TryMap`, and `Refined`;
- dependencies with `Bind` or `Implicit`; and
- bounded recursion with `FixWith`.

The same value implements separate specification traits for parsing,
serialization, byte length, and consistency. Proof traits establish properties
only when the relevant child invariants and side conditions hold. This makes it
possible to represent both canonical and intentionally malleable formats
without assigning either one inaccurate guarantees.

The complete catalog and links to each implementation are in the
[`combinators`](https://secure-foundations.github.io/vest/vest_lib/combinators/)
module. See [What Vest proves](../guarantees.md) before implementing a new
combinator proof.

