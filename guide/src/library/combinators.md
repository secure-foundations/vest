# Using `vest_lib`

**TODO.** This page is not written yet.

Most applications should use the [Vest DSL](../getting-started.md) or the
[ASN.1 frontend](../asn1/index.md), which generate parsers and serializers  for you, composed with format combinators in `vest_lib`.
This page will cover the case where you prefer writing them by hand: when a format is too complex to express in the DSL.

Until then, the
[`combinators` module documentation](../../vest_lib/combinators/index.html)
lists every primitive and higher-order format with its semantics and
[`vest_dev/src/formats`](https://github.com/secure-foundations/vest/tree/main/vest_dev/src/formats)
holds some handwritten examples that demonstrate how to use them.
