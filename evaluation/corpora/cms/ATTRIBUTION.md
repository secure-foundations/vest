# CMS corpus attribution and selection

The timed corpus contains only complete `SignedData` values accepted by VPS, rasn-cms, and
RustCrypto-cms under the rule named below. This common-input policy keeps implementation bars
directly comparable. `MANIFEST.tsv` in each directory records the upstream path, byte count, and
SHA-256 of every retained ContentInfo object; the benchmark removes the ContentInfo wrapper and
times the complete inner SignedData TLV without otherwise rewriting it.

## NIST PKITS (`pkits/`)

- Source: NIST Public Key Interoperability Test Suite 1.0.1,
  <https://csrc.nist.gov/Projects/pki-testing> (`PKITS_data.zip`).
- Provenance: developed by NIST with BAE Systems and NSA. The official archive contains signed
  S/MIME messages for the path-validation cases.
- Extraction: the `application/pkcs7-mime` payload is decoded from each official `.eml` file.
- Rule: BER.
- Upstream coverage: 224 signed messages. Under BER, VPS and rasn accept all 224 and RustCrypto
  accepts 223; the timed three-way intersection therefore retains 223 messages, totaling 954,515
  bytes of SignedData. Under strict DER, VPS accepts 133: the other 91 contain an unsorted
  `CertificateSet`. All 290 certificates embedded by those 91 messages are individually valid DER;
  only their enclosing BER `SET OF` ordering is non-canonical. RFC 5652 requires DER for signed
  and authenticated attributes, not for this outer collection.

## European Commission DSS CAdES (`dss/`)

- Source: the official European Commission Digital Signature Service repository,
  <https://github.com/esig/dss>, commit `4c2129862948bfd53ca1455832260aa17e183cf8`.
- Upstream license: LGPL-2.1; see <https://github.com/esig/dss/blob/master/LICENSE>.
- Selection root: `dss-cades/src/test/resources/validation`, extensions `.p7m`, `.p7s`, `.cms`,
  and `.pkcs7`.
- Rule: BER. No CMS bytes are normalized before parsing.
- Upstream coverage: 112 of 115 candidate binaries contain a SignedData ContentInfo. VPS accepts
  108, rasn 110, and RustCrypto 78; the timed three-way intersection retains 74 messages totaling
  11,400,481 bytes of SignedData. The wider directory intentionally includes malformed negative
  tests, which are not timed as successful parses.

## RFC 4134 (`rfc4134/`)

- Source: RFC 4134, “Examples of S/MIME Messages,”
  <https://www.rfc-editor.org/rfc/rfc4134.txt>.
- Extraction: Appendix A's `|>name` / Base64 / `|<name` records, following the extraction method
  specified by the RFC.
- Rule: BER.
- Coverage: 16 extracted binaries have SignedData wrappers. VPS and rasn accept 9 and RustCrypto
  accepts 7; the timed three-way intersection contains examples 4.1, 4.2, 4.3, 4.5, 4.6, 4.7,
  and 4.10, totaling 8,332 bytes of SignedData. RFC 4134 states that every example was independently checked
  by two implementors.

## Legacy micro-fixtures

`pkits.p7b` and `pkits_ee.p7b` are retained for the original schema smoke test but are not part of
the three timed corpora. They were copied from RustCrypto `cms` 0.3.0-pre.2 and contain certificates
derived from PKITS rather than the official signed S/MIME message set.
