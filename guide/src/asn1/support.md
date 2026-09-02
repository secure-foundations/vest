# Supported ASN.1 and limitations

What `vest_asn1` accepts today.
Anything listed as not supported is _rejected_ by the compiler
with an error.

## Primitive types

| Type                                           | Support             | Notes                                                                                                          |
| ---------------------------------------------- | ------------------- | -------------------------------------------------------------------------------------------------------------- |
| `BOOLEAN`                                      | Supported           |                                                                                                                |
| `INTEGER`                                      | Supported           | support for arbitrary-width big integers; constraint `INTEGER` specializes to the narrow `i8` or `i16` backend |
| `ENUMERATED`                                   | Supported           | supported as a constraint on `INTEGER` (specialized to `i16`)                                                  |
| `NULL`                                         | Supported           |                                                                                                                |
| `OBJECT IDENTIFIER`                            | Supported           | as a type; not as a value assignment                                                                           |
| `REAL`                                         | Supported           | as a type; not as a value assignment                                                                           |
| `OCTET STRING`                                 | Supported           |                                                                                                                |
| `BIT STRING`                                   | Partially supported | no `SIZE` constraints                                                                                          |
| `ANY`                                          | Partially supported | no `ANY DEFINED BY` dispatch                                                                                   |
| `UTF8String`                                   | Supported           |                                                                                                                |
| `PrintableString`                              | Supported           |                                                                                                                |
| `IA5String`                                    | Supported           |                                                                                                                |
| `NumericString`                                | Supported           |                                                                                                                |
| `TeletexString`                                | Partially supported | character-set validation is currently a stub                                                                   |
| `BMPString`                                    | Supported           | no borrowed forms, always owned                                                                                |
| `UniversalString`                              | Supported           | no borrowed forms, always owned                                                                                |
| `UTCTime`                                      | Supported           |                                                                                                                |
| `GeneralizedTime`                              | Supported           |                                                                                                                |
| `GeneralString`                                | Not supported       |                                                                                                                |
| `VisibleString` / `ISO646String`               | Not supported       |                                                                                                                |
| `GraphicString`, `VideotexString`, `T61String` | Not supported       |                                                                                                                |
| `RELATIVE-OID`                                 | Not supported       |                                                                                                                |
| `ObjectDescriptor`, `EXTERNAL`, `EMBEDDED PDV` | Not supported       |                                                                                                                |
| `DATE`, `TIME`, `DURATION`                     | Not supported       |                                                                                                                |

## Constructed types

| Type                        | Support             | Notes                                                                     |
| --------------------------- | ------------------- | ------------------------------------------------------------------------- |
| `SEQUENCE`                  | Supported           |                                                                           |
| `SEQUENCE OF`               | Supported           |                                                                           |
| `SET OF`                    | Supported           | ordering rules differ by encoding rule — see below                        |
| `CHOICE`                    | Supported           |                                                                           |
| `SET`                       | Partially supported | DER only, and fields must already be in canonical tag order in the schema |
| Anonymous inline composites | Supported           | lifted to private helper definitions                                      |
| Recursive schema            | Not supported       |                                                                           |

## Tagging

| Feature                                        | Support       | Notes                                                 |
| ---------------------------------------------- | ------------- | ----------------------------------------------------- |
| `EXPLICIT` tags                                | Supported     |                                                       |
| `IMPLICIT` tags                                | Supported     | replaces the outer tag                                |
| Context-specific, application, private classes | Supported     |                                                       |
| `IMPLICIT` on `CHOICE` or `ANY`                | Supported     | promoted to explicit — neither has one tag to replace |
| `AUTOMATIC TAGS`                               | Not supported |                                                       |

## Components and constraints

| Feature                               | Support             | Notes                                                                 |
| ------------------------------------- | ------------------- | --------------------------------------------------------------------- |
| `OPTIONAL`                            | Supported           |                                                                       |
| `DEFAULT`                             | Partially supported | `BOOLEAN`, `ENUMERATED`, and `INTEGER` whose range fits in `i8`/`i16` |
| `SIZE` — fixed, bounded, one-sided    | Supported           | on strings and collections; not on `BIT STRING`                       |
| `INTEGER` value and range constraints | Supported           |                                                                       |
| `WITH COMPONENTS`                     | Not supported       |                                                                       |
| Extension markers (`...`)             | Not supported       |                                                                       |
| Extension-addition groups             | Not supported       |                                                                       |

## Module-level

| Feature                                              | Support       | Notes                                                                        |
| ---------------------------------------------------- | ------------- | ---------------------------------------------------------------------------- |
| Local type references                                | Supported     |                                                                              |
| `BOOLEAN`, `INTEGER`, `ENUMERATED` value assignments | Supported     | emitted as typed Rust constants                                              |
| `OBJECT IDENTIFIER`, `REAL` value assignments        | Not supported |                                                                              |
| Imports from other modules                           | Not supported | module linking is unimplemented; curate dependencies into one module instead |

## Additional notes

**`SET OF` ordering.** DER requires the values to be sorted by their complete
DER TLV encoding. The generated `prepare` rejects an unsorted vector without
allocating, so sorting is the caller's job (the provided comparison abstraction is non-allocating so sorting should be efficient as well). Duplicate encodings are allowed. BER
`SET OF` imposes no canonical order and preserves schema order on output.

**Heterogeneous `SET`.** BER lets a `SET` carry its components in any order, so
a BER parser would have to accept every permutation of the fields. DER
instead fixes them in ascending tag order. `vest_asn1` currently emits `SET` only
under DER, and only when the schema already lists the fields in canonical order. The `vest_lib` backend supports a group of `Permute` combinators that can be used to implement BER `SET`, but the generator does not yet emit them.

**Borrowing and `alloc`.** DER strings are contiguous, so their value types
borrow from the input. BER strings may arrive fragmented across constructed
encodings and are flattened into owned values, which is why BER modules need the
`alloc` feature where the equivalent DER module may not. `BMPString` and
`UniversalString` are always owned, since their wire form is not UTF-8.

**High tag numbers and disjointness.** `CHOICE`, `OPTIONAL`, and `DEFAULT` need
alternatives/adjacent fields to be provably disjoint. The generated proof covers
the 256 possible leading identifier octets: tags 0 through 30 are exact, but all
high-tag-number forms sharing a class and constructed bit collapse onto one bit.
Two such tags cannot be proven disjoint from their later tag-number octets
alone, so a schema that distinguishes alternatives only by high tag numbers is
conservatively rejected.
