# ASN.1 code-generation scalability

This note records the verification boundaries used by `vest_asn1`, the main
performance problems found during development, and the resulting design. Times
are historical single-run measurements and should be treated as directional;
CI correctness does not depend on them.

## What did not scale

Early generated code exposed deeply nested combinator and mapper definitions to
every enclosing format. Rust type checking stayed below a few seconds even for
large stress schemas, but Verus and SMT work grew nonlinearly:

- a mixed-modifier BER `SEQUENCE` reached the default resource limit at eight
  fields;
- a right-nested 64-way `CHOICE` exceeded a one-minute trial;
- combined one-field `SEQUENCE` and `CHOICE` chains verified at depth 15 in
  about 43 seconds and exceeded one minute at depth 16; and
- repeatedly unfolding generated executable mapper bodies dominated the
  depth-sensitive verification cost.

Adding broad broadcast groups or more local assertions did not solve the
problem. Those approaches gave the solver additional ways to rediscover the
same structural facts and often increased quantifier instantiation.

## Nominal format boundaries

Every generated ASN.1 definition now has a nominal format type. Its private
nested combinator is verified once, while enclosing definitions use the
nominal type's proved trait implementations. Generated structural spec types
are generic over their field or variant types, and datatype-generic inverse
lemmas prove the mapping between user-facing structs/enums and nested
tuples/sums.

Structural conversion functions are opaque outside their small proof boundary.
The nominal macros reveal only the current type's conversion when required by
an executable implementation; they do not reveal child datatype views or
mapper bodies. Generated `CHOICE` trees are balanced rather than right-nested.

With these changes, the combined depth-16 stress fixture verifies in about 15
seconds on the original measurement setup instead of timing out after one
minute. Depth 17 completed in about 29 seconds and depth 18 in about 63 seconds.
The remaining growth was concentrated in executable map verification, showing
that nominal proof boundaries substantially improve—but do not make—cost
independent of datatype nesting.

## ASN.1 start-domain certificates

`CHOICE`, `OPTIONAL`, and `DEFAULT` require adjacent parser domains to be
disjoint. Reconstructing this fact by recursively unfolding combinators was
particularly unstable for generated schemas. The implementation instead uses
a finite certificate for possible first ASN.1 identifier octets:

```rust
pub ghost struct Asn1TagLeadMask {
    pub universal: u64,
    pub application: u64,
    pub context_specific: u64,
    pub private: u64,
}

pub ghost struct Asn1StartDomain {
    pub accepts_empty: bool,
    pub tags: Asn1TagLeadMask,
}
```

Each 64-bit class word assigns bits 0–31 to primitive tags and bits 32–63 to
constructed tags. Tag numbers below 31 therefore have exact, distinct bits.
All high-tag-number forms with the same class and constructed bit share the
corresponding number-31 bit because their first identifier octet is identical.
This is deliberately conservative: the current certificate cannot prove two
such high tags disjoint even when their later base-128 tag-number octets differ.

`HasAsn1Start` connects a certificate to parser semantics. Required pairs use
the left component's domain; choices, optionals, and defaults use bitmap union;
wrappers delegate to their inner format; and `Eof` records acceptance of empty
input. One backend lemma turns disjoint finite certificates into parser-domain
disjointness.

The frontend computes concrete masks and emits local bit-vector proofs only at
real dispatch boundaries. Generated nominal formats expose sealed start
certificates, so parent formats do not reopen their children. A few explicit
boundary equalities remain intentional: they prevent Verus from unfolding
wrapped `Ref`, `Refined`, `Mapped`, and required-pair definitions to rediscover
the same domain.

This design replaced open-ended quantified search with fixed-size bit-vector
reasoning and made the complete curated CMS schema verify reliably. The key
principle is that the backend proves certificate soundness once, while the
frontend uses its schema-wide knowledge to construct the finite certificate at
the cheapest boundary.

## Maintainer guidance

- Keep generated semantic boundaries nominal and avoid exposing child mapper or
  deep-view definitions.
- Prefer balanced trees for large generated alternatives.
- Keep broadcast groups small; use them for generic semantic bridges, not for
  searching a generated schema tree.
- Carry explicit start-domain equalities across nominal boundaries when they
  prevent definition unfolding.
- Exercise changes against the checked-in depth and width fixtures as well as
  the full curated CMS module.
