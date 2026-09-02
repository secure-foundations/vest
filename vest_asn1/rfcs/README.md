# Curated RFC schemas

This directory holds ASN.1 modules transcribed from published RFCs, curated so
that `vest_asn1` can compile them. They are inputs to the verification corpus,
not part of the `vest_asn1` library.

| Schema | Source | Generated module |
| --- | --- | --- |
| [`CMS-RFC5652-Curated.asn1`](CMS-RFC5652-Curated.asn1) | RFC 5652 §12, with structured dependencies from RFC 5280 App. A and RFC 5755 §4 | [`vest_asn1_tests/src/generated_cms.rs`](../../vest_asn1_tests/src/generated_cms.rs) |

The header comment of each schema records its curation rules — what was
expanded, what was replaced by ordinary wire types, and what was deliberately
left out.

## Generating `generated_cms.rs`

The rule is recorded once, in the `generate` target of
[`vest_asn1_tests/Makefile`](../../vest_asn1_tests/Makefile). Regenerate with:

```sh
make -C vest_asn1_tests generate
```

which runs, for this schema:

```sh
cargo run -p vest_asn1 -- --rules ber \
  --der-definition SignedAttributes \
  --der-definition AuthAttributes \
  --der-definition Certificate \
  --der-definition CertificateList \
  --der-definition AttributeCertificate \
  --der-definition AttributeCertificateV1 \
  vest_asn1/rfcs/CMS-RFC5652-Curated.asn1 -o vest_asn1_tests/src/generated_cms.rs
```

CI regenerates and requires `git diff --exit-code` to be empty, so the committed
module and this command cannot drift apart.

## Why BER is the default

RFC 5652 §1 states the design intent for every CMS content type:

> As a general design philosophy, each content type permits single pass
> processing using indefinite-length Basic Encoding Rules (BER) encoding.

and §5.2 confirms that the carried content itself is unconstrained:

> The eContent need not be DER encoded.

So the CMS envelope — `ContentInfo`, `SignedData`, `EnvelopedData`,
`DigestedData`, `EncryptedData`, `AuthenticatedData`, the `RecipientInfo`
family, `SignerInfo`, and the unsigned/unauthenticated/unprotected attribute
sets — is generated under BER.

## Why the overrides are DER

Each override is a structure whose octets are an input to a signature or digest.
A verifier that does not re-encode — and a Vest-generated parser must not
re-encode, since re-encoding is precisely the step that reintroduces
malleability — has to receive those octets already in DER.

| Definition | Authority | Text |
| --- | --- | --- |
| `SignedAttributes` | RFC 5652 §5.3 | "SignedAttributes MUST be DER encoded, even if the rest of the structure is BER encoded." |
| `AuthAttributes` | RFC 5652 §9.1 | "The AuthAttributes structure MUST be DER encoded, even if the rest of the structure is BER encoded." |
| `Certificate` | RFC 5280 §4.1.1.3 | "The signatureValue field contains a digital signature computed upon the ASN.1 DER encoded tbsCertificate." |
| | RFC 5755 §7.3 | "the digest MUST be calculated over the DER encoding of the entire PKC, including the signature value." |
| `CertificateList` | RFC 5280 §5.1.1.3 | "The signatureValue field contains a digital signature computed upon the ASN.1 DER encoded tbsCertList." |
| `AttributeCertificate` | RFC 5755 §7.3 | Same signed-object shape; RFC 5755 §4 profiles ACs on top of RFC 5280. |
| `AttributeCertificateV1` | RFC 5652 §12.2 | Same signed-object shape. Declared obsolete by §10.2.2, but retained for backward compatibility. |

RFC 5652 §1 also says that "signed attributes and authenticated attributes are
the only data types used in the CMS that require DER encoding". That is a
statement about the types CMS itself defines. `Certificate`, `CertificateList`,
and `AttributeCertificate` are imported from RFC 5280 and RFC 5755, and are
governed by those documents.

`vest_asn1` propagates a rule to every transitive child of an overridden
definition without changing its parents, so the six roots above put the whole
X.509 subtree under DER — `TBSCertificate`, `AlgorithmIdentifier`, `Name`,
`RDNSequence`, `Extensions`, `Validity`, `SubjectPublicKeyInfo`, `GeneralName`,
the X.400 `ORAddress` subtree, and `Attribute`/`AttributeValue`. The result is a
62/62 split between DER and BER nominal formats.

`PersonalName` lands in that closure via
`AttributeCertificate → GeneralNames → GeneralName → ORAddress →
BuiltInStandardAttributes`. It has to: it is a heterogeneous `SET`, and BER
permits a `SET` to carry its components in any order, so `vest_asn1` emits
heterogeneous `SET`s only under DER, where X.690 clause 11 fixes them in
ascending tag order and a single fixed-order combinator is sound.

## What is deliberately *not* overridden

`ExtendedCertificate` is a signed object too, but its closure reaches
`UnauthAttributes`, which CMS leaves under BER. Forcing it to DER would make
unauthenticated attributes stricter than RFC 5652 allows. RFC 5652 §10.2.2 also
declares it obsolete:

> The PKCS #6 extended certificate is obsolete. The PKCS #6 certificate is
> included for backward compatibility, and PKCS #6 certificates SHOULD NOT be
> used.

so it stays BER.

## Known strictness deviations

`vest_asn1` gives each definition exactly one rule, so a definition shared
between a DER and a BER context resolves to DER. Two shared definitions in this
schema are therefore stricter than RFC 5652 alone requires:

- **`Attribute` / `AttributeValue`** are DER because `SignedAttributes` and
  `AuthAttributes` reach them. `UnsignedAttributes`, `UnauthAttributes`, and
  `UnprotectedAttributes` remain BER `SET OF`s, but their *elements* must now be
  DER-encoded. RFC 5652 permits BER there.
- **`AlgorithmIdentifier`** is DER because `TBSCertificate` reaches it. The
  aliases `DigestAlgorithmIdentifier`, `SignatureAlgorithmIdentifier`,
  `KeyEncryptionAlgorithmIdentifier`, `ContentEncryptionAlgorithmIdentifier`,
  `MessageAuthenticationCodeAlgorithm`, and `KeyDerivationAlgorithmIdentifier`
  stay BER as parents, but the algorithm identifier they wrap — including the
  one in a BER `SignerInfo` — must be DER-encoded. RFC 5652 permits BER there.

Both narrow the set of accepted encodings; neither accepts anything the RFCs
reject. Splitting the shared definitions in the curated schema would remove them
at the cost of introducing type names that do not appear in the source RFCs.

## Scope

This is a wire schema. It does not express CMS version-selection rules,
algorithm policy, attribute uniqueness, `ANY DEFINED BY` dispatch, or any
cryptographic validation. See
[`dev_docs/asn1-scalability.md`](../../dev_docs/asn1-scalability.md) for how
this module drove the nominal-format and start-domain design.
