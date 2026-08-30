# Supported ASN.1 and limitations

The frontend supports the following current subset:

- BOOLEAN, INTEGER, typed ENUMERATED, OBJECT IDENTIFIER, REAL, NULL, and ANY;
- BIT STRING, OCTET STRING, supported character strings, and time strings;
- SEQUENCE, SEQUENCE OF, SET OF, CHOICE, and statically ordered heterogeneous
  DER SET;
- OPTIONAL and supported DEFAULT components;
- local references and EXPLICIT/IMPLICIT tags in the context-specific,
  application, and private classes; and
- fixed, bounded, and one-sided SIZE constraints for supported strings and
  collections, plus INTEGER value and range constraints.

DER `SET OF` requires values already sorted by complete DER TLV encoding and
allows duplicate encodings. Preparation rejects unsorted values without
allocating. BER `SET OF` preserves schema order. Heterogeneous BER SET is not
yet generated.

DEFAULT values are supported for BOOLEAN, ENUMERATED, and INTEGER types whose
finite constraint selects the current `i8` or `i16` backend.

Current unsupported or restricted constructs include OBJECT IDENTIFIER and
REAL value assignments, large ENUMERATED executable values, BIT STRING SIZE
constraints, RELATIVE-OID, GeneralString, VisibleString, ANY DEFINED BY,
general constraint combinations, imports, AUTOMATIC TAGS, extension markers,
extension-addition groups, WITH COMPONENTS, and recursive schema definitions.
Recognized unsupported syntax is rejected rather than approximated.

Generated first-tag certificates represent the 256 possible identifier-leading
octets. Tags numbered 0 through 30 are exact. High-tag numbers with the same
class and constructed bit share a leading-octet bit, so the current automation
cannot certify two such tags as disjoint solely from later tag-number octets.

The checked fixtures under `vest_asn1_tests` are the executable source of truth
for combinations supported by the current compiler.

