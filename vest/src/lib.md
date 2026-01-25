# Vest

`vest_lib` is a *formally verified* combinator library for parsing and serializing binary data. It is the backend of the [Vest](https://github.com/secure-foundations/vest) framework, which can automatically produce verified parsers and serializers from a high-level format description.

This document primarily serves as a reference for users who want to use the combinator library directly to achieve greater flexibility in the parsing and serialization process. For a more automated workflow, refer to the [`vest`](https://crates.io/crates/vest) crate and some examples of using [Vest DSL](https://github.com/secure-foundations/vest/tree/main/vest-examples#using-the-vest-dsl-with-buildrs).

## Formally Verified Parsing and Serialization

Vest leverages the Rust type system and [Verus](https://github.com/verus-lang/verus) to formally verify 
the correctness and security of binary parsing and serialization. We exploit
Rust's borrowing, lifetime, and the powerful trait system to achieve
high-performance without sacrificing safety, while Verus allows us to specify
and prove key [round-trip](properties/trait.SecureSpecCombinator.html#tymethod.theorem_serialize_parse_roundtrip) [properties](properties/trait.SecureSpecCombinator.html#tymethod.theorem_parse_serialize_roundtrip) about our combinators.

These properties ensure mutual inversion of parsing and serialization, making them immune to 
[parser malleability](properties/trait.SecureSpecCombinator.html#method.corollary_parse_non_malleable) and [format confusion attacks](properties/trait.SecureSpecCombinator.html#method.corollary_serialize_injective_contraposition). See more in our [USENIX Security '25 paper](https://www.andrew.cmu.edu/user/bparno/papers/vest.pdf).

## Available Combinators

Vest provides a small yet expressive set of formally verified combinators for building parsers and serializers. 
Each combinator's correctness properties are verified once and can be reused across complex compositions.

| Combinator | Purpose |
|------------|---------|
| [`bytes::Fixed`](regular/bytes/struct.Fixed.html) | Parse and serialize a fixed number of bytes (compile-time known) |
| [`bytes::Variable`](regular/bytes/struct.Variable.html) | Parse and serialize a dynamic number of bytes (runtime known) |
| [`U8`](regular/uints/struct.U8.html)/[`U16Le`](regular/uints/struct.U16Le.html)/[`U32Le`](regular/uints/struct.U32Le.html)/[`U64Le`](regular/uints/struct.U64Le.html) | Parse and serialize unsigned integers in little-endian format |
| [`U16Be`](regular/uints/struct.U16Be.html)/[`U32Be`](regular/uints/struct.U32Be.html)/[`U64Be`](regular/uints/struct.U64Be.html) | Parse and serialize unsigned integers in big-endian format |
| [`UnsignedLEB128`](regular/leb128/struct.UnsignedLEB128.html) | Parse and serialize unsigned integers using LEB128 variable-length encoding |
| [`BtcVarint`](bitcoin/varint/struct.BtcVarint.html) | Parse and serialize unsigned integers using Bitcoin's VarInt variable-length encoding |
| [`Pair`](regular/sequence/struct.Pair.html) | Sequentially compose two combinators, where the second might *depend on* the first's output |
| [`Preceded`](regular/sequence/struct.Preceded.html) | Sequentially compose two combinators, omitting the first's output |
| [`Terminated`](regular/sequence/struct.Terminated.html) | Sequentially compose two combinators, omitting the second's output |
| [`Choice`](regular/variant/struct.Choice.html) | Try two combinators *in order* |
| [`RepeatN`](regular/repetition/struct.RepeatN.html) | Repeat a combinator a fixed number of times |
| [`Repeat`](regular/repetition/struct.Repeat.html) | Repeat a combinator until the end of input buffer |
| [`Refined`](regular/modifier/struct.Refined.html) | Refine parsed/serialized values with predicates |
| [`Mapped`](regular/modifier/struct.Mapped.html) | Transform parsed/serialized values with infallible isomorphisms |
| [`TryMap`](regular/modifier/struct.TryMap.html) | Transform parsed/serialized values with fallible isomorphisms |
| [`Cond`](regular/modifier/struct.Cond.html) | Conditionally apply a combinator based on a predicate |
| [`AndThen`](regular/modifier/struct.AndThen.html) | Re-interpret bytes with (potentially nested) sub-combinators |
| [`Opt`](regular/modifier/struct.Opt.html) | Optionally apply a combinator |
| [`Success`](regular/success/struct.Success.html) | Always succeeds and consumes nothing (unit combinator) |
| [`Fail`](regular/fail/struct.Fail.html) | Always fails with a custom error message |
| [`End`](regular/end/struct.End.html) | Succeeds only at the end of input buffer |
| [`Tag`](regular/tag/struct.Tag.html) | Match a specific value (useful for format markers) |

## Examples

### Parsing and serializing a pair of bytes

```rust
# use std::error::Error;
# fn main() -> Result<(), Box<dyn Error>> {
use vest_lib::regular::bytes::Fixed;
use vest_lib::properties::Combinator;

// Define a combinator for parsing two consecutive fixed-size byte sequences
let pair_of_bytes = (Fixed::<1>, Fixed::<2>);

let input = &[0x10, 0x20, 0x30][..];
let (consumed, (a, b)) = <_ as Combinator<&[u8], Vec<u8>>>::parse(&pair_of_bytes, input)?;

let mut output = vec![0x00; 10];
let written = <_ as Combinator<&[u8], Vec<u8>>>::serialize(&pair_of_bytes, (&a, &b), &mut output, 0)?;

assert_eq!(written, consumed);
assert_eq!(&output[..written], &input[..consumed]);
# Ok(())
# }
```

### Refining parsed values with predicates

```rust
# use std::error::Error;
# fn main() -> Result<(), Box<dyn Error>> {
use vest_lib::regular::uints::U8;
use vest_lib::regular::modifier::{Refined, Pred, SpecPred};
use vest_lib::properties::Combinator;
use vstd::prelude::*;

verus! {
    pub struct EvenU8;
    impl View for EvenU8 {
        type V = Self;
        open spec fn view(&self) -> Self::V { *self }
    }

    impl SpecPred<u8> for EvenU8 {
        open spec fn spec_apply(&self, i: &u8) -> bool {
            *i % 2 == 0
        }
    }

    impl Pred<u8> for EvenU8 {
        fn apply(&self, i: &u8) -> bool {
            *i % 2 == 0
        }
    }
}

// Create a refined combinator that only accepts even numbers
let even_u8 = Refined { inner: U8, predicate: EvenU8 };

// Serialize an even number
let mut output = vec![0x00; 10];
let written = <_ as Combinator<&[u8], Vec<u8>>>::serialize(&even_u8, &10u8, &mut output, 0)?;

// Parse it back - this succeeds because 10 is even
let (consumed, parsed) = <_ as Combinator<&[u8], Vec<u8>>>::parse(&even_u8, &output[..written])?;
assert_eq!(parsed, 10);
# Ok(())
# }
```
