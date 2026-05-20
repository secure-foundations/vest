# Sources of Malleability Across Binary Formats

This note groups together **recurring sources of malleability** seen across binary formats used in networking, cryptography, archives, images, databases, filesystems, and storage engines.

Here, **malleability** means that the same higher-level meaning, object, or observable content can be represented by more than one legal byte sequence, or that a decoder may accept more than one wire/storage form that applications would treat as “the same enough.”

This is **not** always bad. Many formats deliberately keep such flexibility for streaming, compression, forward compatibility, or implementation freedom. But if bytes are hashed, signed, used as a cache key, or fed into consensus logic, these freedoms become security-relevant.

---

## Summary table

| Category                                                    | Mechanism                                                                                                       | Representative formats                                                                                                                                                                                                                                     | What the flexibility buys                                                      | Security / robustness risk                                                                                                | Typical mitigation                                                                             |
| ----------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------- |
| **1. Indirection / pointer-based reuse**                    | Replacing repeated content with pointers, references, or deltas to prior content                                | **DNS** name compression pointers; **Git packfiles** `ofs-delta` / `ref-delta`; some archive formats with links                                                                                                                                            | Smaller messages/files; better compression; reuse of prior material            | Pointer loops, out-of-bounds jumps, aliasing, confusing “same content / different bytes” issues                           | Canonicalize by forbidding indirection in signed form, or require validated acyclic references |
| **2. Ordering freedom**                                     | Fields, payloads, chunks, map entries, or sections may appear in more than one order                            | **TLS** extension ordering; **IKEv2** payload ordering; **Protobuf** field order; **PNG** ancillary chunk order                                                                                                                                            | Implementation freedom; optimization; compatibility                            | Different bytes for same semantics; parser disagreements; fingerprinting side effects                                     | Sort before signing / hashing, or sign exact transmitted bytes                                 |
| **3. Duplicate-entry / duplicate-key / shadowing freedom**  | Multiple entries with the same name/key/tag are allowed or tolerated                                            | **CBOR** duplicate map keys; **BSON/MongoDB** duplicate field names; some archive/container formats with repeated metadata                                                                                                                                 | Loose extensibility and compatibility                                          | First-wins vs last-wins ambiguity; inconsistent query/verification results                                                | Reject duplicates in critical contexts                                                         |
| **4. Multiple primitive encodings / non-minimal encodings** | Same integer, length, float, or atom can be written in more than one legal low-level form                       | **BER** vs **DER**; **CBOR** preferred vs non-preferred integer/float widths; permissive varint encodings in some systems; non-canonical SIGHASH encodings in older cryptocurrency protocols                                                               | Flexibility, easy streaming, backwards compatibility                           | Signature/hash malleability; parser differentials; replay or cache confusion                                              | Require shortest/minimal encodings; distinguished/canonical rules                              |
| **5. Chunking / blocking / segmentation freedom**           | Same logical content split into different block/page/chunk shapes                                               | **CBOR** indefinite-length items; **Avro** array/map blocks; **PNG** multiple `IDAT` chunks; **ZIP** optional data descriptor; **tar** optional EOF markers                                                                                                | Streaming and incremental writing; random access; compression tuning           | Different bytes for same data; parser bugs around boundary handling                                                       | Deterministic profile: fixed chunking, no indefinite-length forms                              |
| **6. Compression / filter / codec choice freedom**          | Same content compressed or preconditioned in different ways                                                     | **PNG** scanline filters + deflate block choices; **Btrfs** ZLIB/LZO/ZSTD and per-extent compression; **Parquet** page encodings; **Git** delta-vs-base representation                                                                                     | Better space/time tradeoffs                                                    | Same visible content, many byte-level forms; decompression bombs; verifier mismatch if bytes are authenticated indirectly | Authenticate exact bytes, or decode to canonical form then re-encode                           |
| **7. Redundant metadata / alternate metadata channels**     | Same logical metadata can live in multiple places or optional side records                                      | **ZIP** local header vs central directory vs extra fields vs data descriptor; **tar** ustar vs PAX headers; **PNG** `tEXt`/`zTXt`/ancillary chunks                                                                                                         | Backwards compatibility; richer metadata; streaming                            | Inconsistent shadow copies; selective parser use; “signed one copy, consumed another”                                     | Define one authoritative source of truth; reject inconsistent copies                           |
| **8. Storage-layout / allocator freedom**                   | Same logical dataset or file tree can have different on-disk placement, free-space maps, and housekeeping pages | **SQLite** freelist / autovacuum / text encoding / legacy file-format options; **Parquet** row-group/page layout and encoding choices; **ext4** delayed allocation and block-group placement; **XFS** inode placement; **Btrfs** extent layout/compression | Performance tuning, fragmentation control, crash recovery, incremental updates | No stable bytes for “same database/filesystem contents”; fragile hashing / notarization if done over raw images           | Define canonical export / dump form, not raw on-disk image                                     |
| **9. Optional / ancillary / advisory content freedom**      | Optional chunks/fields may be present, absent, repeated, or ignored without changing core content               | **PNG** ancillary chunks; **ZIP** comments and extra fields; **SQLite** application ID/user version; **Parquet** optional encodings/statistics                                                                                                             | Rich metadata; extensibility                                                   | Ambiguity about whether metadata is authenticated or semantically relevant                                                | Separate signed core content from unsigned advisory metadata                                   |
| **10. Case / normalization freedom**                        | Same semantic name/text represented with different case or normalized forms                                     | **DNS** names in ordinary wire format vs DNSSEC canonical form; text-bearing formats more generally                                                                                                                                                        | Human convenience and compatibility                                            | Signature mismatch, cache inconsistency, parser differentials                                                             | Normalize before signing/hashing                                                               |
| **11. Version / profile freedom**                           | Same logical object can be serialized under different format revisions or profiles                              | **SQLite** legacy/new file format; **ZIP64** vs classic ZIP; **tar** ustar/PAX/GNU variants                                                                                                                                                                | Evolution without immediate breakage                                           | Same content, different bytes; downgrade/upgrade confusion                                                                | Version pinning; canonical profile selection                                                   |

---

## Detailed categories with examples

### 1. Indirection / pointer-based reuse

This is the family you pointed out with **DNS**.

- **DNS** message compression lets a domain name be represented as a full label sequence, a pointer, or a label sequence ending in a pointer. RFC 1035 explicitly allows all three forms. See RFC 1035 §4.1.4: “an entire domain name or a list of labels at the end of a domain name is replaced with a pointer to a prior occurrence of the same name.”  
  Source: <https://datatracker.ietf.org/doc/html/rfc1035>
- **DNSSEC** then has to _remove_ that freedom for signing: RFC 4034 requires that every domain name in the signed RR be fully expanded (**no compression**) and lowercased where applicable.  
  Source: <https://datatracker.ietf.org/doc/html/rfc4034>
- **Git packfiles** can store an object directly or as `ofs-delta` / `ref-delta`, where reconstruction depends on a base object.  
  Source: <https://git-scm.com/docs/pack-format>

**What this flexibility buys:** compactness and reuse.

**What can go wrong:** pointer loops, out-of-bounds references, aliasing, and multiple byte-level representations for effectively the same decoded object. DNS is the classic example: RFC 9267 documents out-of-bounds compression pointers and infinite pointer loops leading to DoS or worse.  
Source: <https://datatracker.ietf.org/doc/html/rfc9267>

---

### 2. Ordering freedom

The same payload set or metadata set may be legal in several orders.

- **IKEv2** says implementations _should_ send payloads in the RFC’s order, but receivers **must not reject** messages merely because payloads appear in another order.  
  Source: <https://datatracker.ietf.org/doc/html/rfc7296>
- **TLS 1.3** allows extension ordering freedom (subject to some local constraints like `pre_shared_key` placement), which is why extension-order randomization is possible and affects fingerprinting.
- **Protobuf** does not define a canonical field order for generic serialization.
- **PNG** critical chunks have stronger order rules, but ancillary chunks “are listed in alphabetical order” in the spec and “this is not necessarily the order in which they would appear in a file.”  
  Source: <https://www.w3.org/TR/PNG-Chunks.html>

**What this flexibility buys:** implementation freedom, compatibility, optimization, reduced parser coupling.

**What can go wrong:** byte instability, parser differentials, or unintended fingerprinting features.

---

### 3. Duplicate-entry / duplicate-key / shadowing freedom

A format may allow repeated names/keys, leaving resolution policy to applications or implementations.

- **CBOR** is a major example: duplicate map keys are possible in general CBOR and must be handled by the protocol profile.
- **BSON / MongoDB** documents with duplicate field names are explicitly warned against. MongoDB’s docs say insertion may silently drop duplicate values or may insert an invalid document with duplicate field names, and querying can then yield inconsistent results.  
  Source: <https://www.mongodb.com/docs/manual/core/document/>

**What this flexibility buys:** loose extensibility, compatibility with simple encoders, less up-front schema strictness.

**What can go wrong:** first-wins / last-wins differences, signature confusion, and mismatches between what one layer verifies and another layer consumes.

---

### 4. Multiple primitive encodings / non-minimal encodings

The same scalar can often be written in several different legal forms unless the format/profile forbids it.

- **ASN.1 BER** is the archetype: lengths, forms, and encodings are flexible. **DER** exists to remove that freedom and force one distinguished encoding.
- **CBOR** can encode numbers and lengths in more than one way unless the deterministic profile is enforced.
- **RLP** and **Bencode** are notable because they deliberately _forbid_ some malleable forms, such as leading-zero integer encodings, to keep a unique representation.

**What this flexibility buys:** easy encoding, compatibility, and sometimes better streaming support.

**What can go wrong:** signature/hash malleability and cross-implementation disagreement.

---

### 5. Chunking / blocking / segmentation freedom

Even if each primitive is encoded uniquely, the same sequence may be split differently.

- **CBOR** indefinite-length strings/arrays/maps versus definite-length ones.
- **Avro** arrays and maps are serialized in one or more blocks, and negative counts add explicit block-size information for skipping.  
  Source: <https://avro.apache.org/docs/current/specification/>
- **PNG** requires one or more `IDAT` chunks; multiple `IDAT`s are legal as long as they are consecutive.  
  Source: <https://www.w3.org/TR/PNG-Chunks.html>
- **ZIP** may include or omit a data descriptor after file data, and the descriptor itself may appear with or without the commonly adopted signature `0x08074b50`.  
  Source: <https://pkware.cachefly.net/webdocs/casestudies/APPNOTE.TXT>
- **tar** readers must not assume the two 512-byte zero blocks marking EOF are present, even though writers should usually emit them.  
  Source: <https://www.gnu.org/software/tar/manual/html_chapter/Tar-Internals.html>

**What this flexibility buys:** streaming, appendability, damage recovery, and skip-ability.

**What can go wrong:** lots of byte-level forms for the same logical content; tricky boundary bugs.

---

### 6. Compression / filter / codec choice freedom

The same uncompressed content can be represented by many valid compressed forms.

- **PNG** is a strong example: encoders can choose scanline filter algorithms on a scanline-by-scanline basis, and the resulting filtered bytes are then compressed with deflate, which itself has many valid block/Huffman choices.  
  Sources: <https://www.libpng.org/pub/png/spec/1.2/PNG-Filters.html>, <https://w3c.github.io/png/>
- **Btrfs** supports transparent compression with **ZLIB**, **LZO**, or **ZSTD**, chosen per file/extent, and data are chunked before compression.  
  Source: <https://btrfs.readthedocs.io/en/latest/Compression.html>
- **Parquet** supports many encodings for the same physical/logical values: PLAIN, dictionary, RLE/bit-packing, delta encodings, byte-stream split, etc.  
  Source: <https://parquet.apache.org/docs/file-format/data-pages/encodings/>
- **Git packfiles** may store the same object directly or in deltified form.  
  Source: <https://git-scm.com/docs/pack-format>

**What this flexibility buys:** smaller files and better performance.

**What can go wrong:** byte instability for visible-identical content, decompression bombs, and canonicalization challenges for signed artifacts.

---

### 7. Redundant metadata / alternate metadata channels

Some formats intentionally store overlapping metadata in several places.

- **ZIP** has metadata in local headers, central directory headers, extra fields, comments, and optional data descriptors. The spec explicitly notes extra metadata redundancy in local headers and central directory handling; central-directory encryption can even mask local-header fields with placeholders.  
  Source: <https://pkware.cachefly.net/webdocs/casestudies/APPNOTE.TXT>
- **tar** PAX headers layer extended metadata on top of base ustar headers.  
  Source: <https://www.gnu.org/software/tar/manual/html_chapter/Tar-Internals.html>
- **PNG** allows visible image data plus optional text / compressed-text / ancillary chunks that many decoders ignore.  
  Source: <https://www.w3.org/TR/PNG-Chunks.html>

**What this flexibility buys:** backward compatibility and richer metadata.

**What can go wrong:** “which copy is authoritative?” issues, especially if one layer signs or validates one copy while another consumes another copy.

---

### 8. Storage-layout / allocator freedom

This is the major extra family often missed in networking-centric surveys.

These formats are not just serializations of values; they are **storage engines** or **on-disk data structures**. The same logical contents can map to many different legal byte layouts because physical placement, free-space management, compression, and optimization policies are part of the format.

#### SQLite

SQLite database files are full of storage-policy choices that are not part of SQL-level meaning:

- unused pages live on a **freelist**;
- **auto_vacuum / incremental_vacuum** alter whether pointer-map pages are present;
- text strings may be stored as **UTF-8**, **UTF-16LE**, or **UTF-16BE** depending on the file header;
- legacy/new file-format options exist, and `VACUUM` can recreate the database file in a new format.  
  Sources: <https://sqlite.org/fileformat.html>, <https://tool.oschina.net/uploads/apidocs/sqlite/formatchng.html>

This means that “same tables and rows” does **not** imply “same bytes on disk.”

#### Parquet

Parquet also has layout-level malleability:

- a file is divided into one or more **row groups**;
- row groups contain **column chunks**;
- column chunks contain one or more **pages**;
- pages may use different **encodings** and compression strategies.  
  Sources: <https://parquet.apache.org/docs/concepts/>, <https://parquet.apache.org/docs/file-format/data-pages/encodings/>

Same logical table, many legal physical layouts.

#### Filesystems (ext4, XFS, Btrfs)

Filesystems are especially layout-malleable:

- **ext4** uses speculative allocation, delayed allocation, block-group placement, and locality heuristics, so the same namespace-level file contents may land in different extents and block groups.  
  Source: <https://docs.kernel.org/filesystems/ext4/allocators.html>
- **XFS** supports different inode-placement strategies (`inode32` vs `inode64`, allocator modes, etc.), affecting legal on-disk layouts.  
  Source: <https://docs.kernel.org/admin-guide/xfs.html>
- **Btrfs** can store different files or extents compressed with different algorithms and chunking choices.  
  Source: <https://btrfs.readthedocs.io/en/latest/Compression.html>

For filesystems, raw-image hashing is therefore usually the **wrong abstraction** if the goal is to authenticate a logical directory tree.

---

### 9. Optional / ancillary / advisory content freedom

A format may distinguish between core content and optional side information.

- **PNG** ancillary chunks are optional, can be ignored by decoders, and need not appear in the summary-table order. Multiple `tEXt` chunks and even multiple chunks with the same keyword are allowed.  
  Source: <https://www.w3.org/TR/PNG-Chunks.html>
- **ZIP** comments and extra fields are optional and may encode the same human-meaningful metadata through several mechanisms.  
  Source: <https://pkware.cachefly.net/webdocs/casestudies/APPNOTE.TXT>
- **SQLite** has application-level header fields like user version and application ID that are orthogonal to SQL table contents.  
  Source: <https://sqlite.org/fileformat.html>

**Risk:** “same visible content” can still have many distinct legal files because advisory metadata differs.

---

### 10. Case / normalization freedom

Even when the binary structure is fixed, text-like subcomponents may admit several equivalent spellings.

- **DNS** names in general operation are case-insensitive, but **DNSSEC** canonicalization requires full expansion and lowercasing for signed forms.  
  Source: <https://datatracker.ietf.org/doc/html/rfc4034>

This is a good example of a protocol that had to add a signing-specific canonical form because the ordinary operational representation was too malleable.

---

### 11. Version / profile freedom

Same logical content, different legal profiles/versions.

- **SQLite** legacy and newer file-format choices, autovacuum variants, and `VACUUM`-triggered rewrites show that the on-disk file is version/profile-sensitive.  
  Source: <https://tool.oschina.net/uploads/apidocs/sqlite/formatchng.html>
- **ZIP** classic vs ZIP64 and optional central-directory compression/encryption change the byte-level archive while preserving archive contents.  
  Source: <https://pkware.cachefly.net/webdocs/casestudies/APPNOTE.TXT>
- **tar** variants (ustar, GNU, PAX) provide similar member trees with different header strategies.  
  Source: <https://www.gnu.org/software/tar/manual/html_chapter/Tar-Internals.html>

---

## Compact cross-format mapping

| Format             | Main malleability sources                                                                                       |
| ------------------ | --------------------------------------------------------------------------------------------------------------- |
| **DNS**            | name compression pointers; case normalization freedom in ordinary operation; canonical DNSSEC form removes both |
| **IKEv2**          | payload ordering freedom; encrypted inner payload sequence                                                      |
| **TLS**            | extension ordering freedom; optional extensions                                                                 |
| **BER / ASN.1**    | non-distinguished primitive encodings, length encodings, ordering/canonicalization issues                       |
| **CBOR**           | duplicate keys, indefinite-length items, non-preferred numeric encodings, tagging / representation choices      |
| **Protobuf**       | field ordering freedom, unknown fields, omission/presence of defaults, wire-level non-canonicality              |
| **PNG**            | filter choice, deflate freedom, ancillary chunk ordering/presence, multiple `IDAT`s                             |
| **ZIP**            | local-vs-central metadata redundancy, optional data descriptors, extra fields, ZIP64/profile differences        |
| **tar/PAX**        | base headers plus PAX/GNU extension mechanisms, optional EOF markers                                            |
| **SQLite**         | freelist state, autovacuum pointer maps, text encoding, legacy/new file formats, VACUUM rewrites                |
| **Parquet**        | row-group/page layout, multiple encodings and compression methods                                               |
| **ext4/XFS/Btrfs** | allocator/placement policy, inode/extents placement, compression choices, storage-engine housekeeping           |
| **Git packfiles**  | direct vs deltified object storage; offset vs reference deltas                                                  |
| **BSON/MongoDB**   | duplicate field names and inconsistent duplicate resolution                                                     |

---

## High-level lesson

Most malleability in binary formats comes from one or more of these deeper causes:

1. **aliasing by indirection** (pointers, deltas, links),
2. **underspecified ordering**,
3. **underspecified uniqueness** (duplicates, shadow copies),
4. **non-minimal primitive encodings**,
5. **streaming-oriented segmentation freedom**,
6. **performance/storage-policy freedom** (compression, allocation, layout), or
7. **metadata channels not tightly tied to core semantics**.

For security-critical use, the usual answer is **not** “ban flexible formats everywhere,” but rather:

- define a **canonical profile** for the bytes being signed or hashed,
- or authenticate the **exact bytes on the wire / disk export**,
- or move signing above the storage format and sign a canonical logical model instead.

## Vest's take on malleability

Maybe the cleanest design is to have a **non-malleable** parse tree layer of wire/on-disk formats, and then another (mapping) layer of logical contents that can be more flexible (hence malleable). For example, a VarInt with multiple legal encodings can be parsed into one of the variants using nested `Choice`s, but then a lossy mapping can convert all variants to a single logical integer.

Distinguish `LossyMapper` from `LosslessMapper` and implement malleable and non-malleable `BerBool` and `VarInt` as examples of using them.

### Controlled Malleability

**DSL**:

- Omitted fields are by default malleable, but can be made non-malleable by
  - being a `const` field, or
  - having a `default` value that is checked against during parsing.
  - being a refinement field with unique value, or
  - being a dependent field whose value can be uniquely determined from other fields or
- Formats containing malleable components (either primitives or user-defined formats) are malleable (e.g., structs with malleable fields, or choices with malleable branches).
- _Unordered_ structs are malleable unless they contain only one field, in which case they are non-malleable (since there is only one possible order).
  **Streaming and Error Tolerance related**:
- Same fields can occur multiple times, with only the last one taking effect (e.g., `CBOR` duplicate map keys, `Protobuf` patchable fields, etc.)
- Fields can be chunked or segmented in multiple ways (e.g., `CBOR`/`ASN.1 BER` indefinite-length items, `Protobuf` repeated fields, etc.)
- Structs/formats themselves can be chunked/segmented (e.g., `Protobuf` messages)

**Combinators**:

- `Mapped` formats with `LossyMapper` are malleable, while those with `LosslessMapper` are non-malleable.
- `Alt` of formats is malleable, unless all alternatives share non-overlapping codomain (disjoint values)
- `Preceded`/`Terminated` are malleable, unless the omitted prefix/suffix admits a unique value, or there is a "default" value for the omitted field that is checked against during parsing.
- `Implicit` omits the preceding field, but is always non-malleable, because it ensures the information of the omitted field is still present in the resulting value (i.g., the value of the omitted field can be determined and recovered from the parsed result).
- `Permute::<N>` is malleable unless `N == 1`
- `Pair`/`Choice` of formats is malleable if either component is malleable, otherwise non-malleable.
- `RepeatN`/`Repeat`/`Array` of formats is malleable if the repeated format is malleable, otherwise non-malleable.
