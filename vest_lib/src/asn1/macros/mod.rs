//! Verified nominal wrappers for ASN.1 schemas.
//!
//! [`impl_der!`](crate::impl_der) and [`impl_ber!`](crate::impl_ber) turn a schema
//! built from combinators into a named format with its own specifications,
//! proofs, and executable APIs. `vest_asn1` emits these macro invocations.
//!
//! # What the caller supplies
//!
//! The invocation names the format kind, value ownership, nominal format type,
//! inner combinator type, specification value type, and executable value type:
//!
//! ```rust,ignore
//! vest_lib::impl_der!(
//!     tag(constructed), borrowed,
//!     HEADER, HEADER__, HeaderSpec, Header,
//!     HeaderForward, HeaderReverse
//! );
//! ```
//!
//! `borrowed` means the executable type is `Header<'i>`; pass just `Header`.
//! `owned` takes a complete type with no input lifetime, such as `bool` or `Vec<u8>`.
//! The optional final arguments name the forward and reverse mappers of a
//! structural `Mapped<_, BiMap<_, _>>`. Its specification value type supplies
//! `lemma_into_from` for the mapper's losslessness proof. Omit these arguments
//! for primitive formats and named aliases.
//!
//! The format must provide a `schema()` constructor usable in both specification
//! and executable code, and `lemma_schema_unambiguous` proving the inner format's
//! `unambiguous()` condition. Certified start domains also require that lemma to
//! equate the inner and nominal `asn1_start()` domains, as in the example below.
//!
//! # Example: a retaggable DER BOOLEAN
//!
//! This is a small version of the code emitted for `Flag ::= BOOLEAN`:
//!
//! ```rust,ignore
//! use vest_lib::asn1::*;
//! use vest_lib::asn1::der_ord::DerState;
//! #[cfg(verus_keep_ghost)]
//! use vest_lib::asn1::disjoint::{
//!     asn1_start_exact_uint, lemma_asn1_start_exact_uint, HasAsn1Start,
//! };
//! use vest_lib::prelude::*;
//!
//! verus! {
//! #[derive(Clone, Copy)]
//! pub struct FlagFmt(pub Class, pub u64);
//!
//! impl FlagFmt {
//!     pub const Fmt: Self = Self(Class::Universal, 1);
//!
//!     #[verifier::allow_in_spec]
//!     pub const fn schema() -> BoolTlvFmt
//!         returns BOOLEAN,
//!     {
//!         BOOLEAN
//!     }
//!
//!     proof fn lemma_schema_unambiguous(&self)
//!         ensures
//!             self.spec_inner().unambiguous(),
//!             self.spec_inner().asn1_start() == self.asn1_start(),
//!     {
//!         reveal(asn1_start_exact_uint);
//!         lemma_asn1_start_exact_uint(self.0, false, self.1);
//!     }
//! }
//! } // verus!
//!
//! vest_lib::impl_der!(tag(primitive), owned, FlagFmt, BoolTlvFmt, bool, bool);
//! // FlagFmt::Fmt.parse(...), .prepare(...), .serialize(...), and .length(...)
//! // are now available, together with the proof traits.
//! ```
//!
//! # Format kinds
//!
//! A named ASN.1 format needs two pieces of tagging information:
//! (1). whether its outer tag can be replaced (for IMPLICIT retagging);
//! and (2). which tags (start_domain) are allowed in a successful parse.
//! The latter lets Vest prove that CHOICE branches, or an OPTIONAL/DEFAULT field and its
//! continuation, are disjoint without unfolding their schemas. The format kind
//! selects the `Retaggable` implementation and the `HasAsn1Start` certificate.
//!
//! An ASN.1 identifier carries a class, a primitive/constructed bit, and a tag
//! number. For example, `BOOLEAN` has universal primitive tag 1 (`01`), while
//! `SEQUENCE(...)` has universal constructed tag 16 (`30`). Identifier octets
//! below are hexadecimal. Vest supports:
//!
//! - **IMPLICIT tagging:** replace the outer class and number, preserving the
//!   content's primitive/constructed form. `IMPLICIT(0, BOOLEAN)` starts with
//!   context-specific primitive tag 0 (`80`), not the BOOLEAN identifier `01`.
//! - **EXPLICIT tagging:** add a constructed TLV around the complete inner TLV.
//!   `EXPLICIT(0, BOOLEAN)` starts with `a0` and retains the inner `01` identifier.
//!   This also gives CHOICE and ANY, which have no single outer tag to replace,
//!   a retaggable envelope.
//!
//! These constructors use the context-specific class; their `_APPLICATION` and
//! `_PRIVATE` variants select those classes instead. `Retaggable` lifts through
//! `Ref`, `Refined`, and `Mapped`, so constraints and value mappings do not prevent
//! replacing the enclosing format's tag.
//!
//! ## A replaceable outer tag: `tag(form)`
//!
//! These formats have one replaceable outer class and number. The form selects
//! whether the start certificate permits primitive, constructed, or both kinds
//! of identifiers:
//!
//! - **`tag(primitive)`**: `Flag ::= BOOLEAN` has universal primitive tag 1 (`01`).
//!   DER `Payload ::= OCTET STRING` also uses this kind, with identifier `04`.
//! - **`tag(constructed)`**: `Record ::= SEQUENCE { flag BOOLEAN }` has universal
//!   constructed tag 16 (`30`). An EXPLICIT envelope also uses this kind:
//!   `[0] EXPLICIT BOOLEAN` starts with constructed identifier `a0`.
//! - **`tag(either)`**: BER `Payload ::= OCTET STRING` accepts primitive `04` and
//!   constructed `24`. After `IMPLICIT(0, PAYLOAD::Fmt)`, the corresponding
//!   identifiers are `80` and `a0`. The schema handles normalization of the
//!   serialized form; there is no separate constructed-bit argument.
//!
//! The kind describes the schema's accepted forms; it does not change the
//! schema's parser or enable constructed encodings by itself.
//!
//! ## A fixed start domain: `starts(domain)`
//!
//! CHOICE and ANY have no single outer tag to replace. Their nominal types are
//! zero-sized and expose a start-domain certificate, without implementing
//! `Retaggable`. Both use `starts(domain)`:
//!
//! - `Selection ::= CHOICE { flag BOOLEAN, count INTEGER }` can start with `01`
//!   or `02`, so it uses `starts(asn1_start_mask(false, 0x6u64, 0, 0, 0))`.
//!   Bits 1 and 2 of the universal-class bitmap are set; the selected alternative
//!   supplies the identifier, not CHOICE itself.
//! - `OpenValue ::= ANY` uses `starts(asn1_start_any_non_eoc())`. It can accept,
//!   for example, an INTEGER TLV beginning with `02` or a SEQUENCE beginning
//!   with `30`, but not standalone end-of-contents (`00 00`). This is an ordinary
//!   start-domain expression, not a separate ANY-specific macro kind.
//!
//! Start-domain masks describe identifier leading octets conservatively; distinct
//! high tag numbers can share a bit. See
//! [`Asn1StartDomain`](crate::asn1::disjoint::Asn1StartDomain) for that limitation.
//!
//! # DER and BER
//!
//! Both macros implement the codec specifications, `SafeParser`, `SoundParser`,
//! `Productive`, `NonTailFmt`, `GoodSerializer`, `SPRoundTripDps`, both serializer
//! equivalence traits, and the executable `Parser`, `Serializer`, `Prepare`, and
//! `ByteLen` APIs. DER additionally implements `StrictParser`, `NonMalleable`, and
//! allocation-free `DerOrd`. The inner format must support the delegated traits.
//!
//! For a BER schema, use BER combinators in `schema()` and invoke `impl_ber!`:
//!
//! ```rust,ignore
//! vest_lib::impl_ber!(
//!     tag(constructed), borrowed,
//!     ITEM, ITEM__, ItemSpec, Item,
//!     ItemForward, ItemReverse
//! );
//! ```
//!
//! Changing the macro alone does not change the schema's encoding rules. BER
//! does not generally preserve encoded length or have a unique encoding, so its
//! macro does not add `StrictParser`, `NonMalleable`, or `DerOrd` implementations.
//!
//! # Proof boundaries and maintenance
//!
//! The nominal specifications are opaque. Proofs reveal only the operations they
//! delegate, and establish the inner invariants locally. The nominal invariants
//! retain their default `true` definitions: parents use the proved properties
//! without rechecking the child's combinator tree.
//!
//! Mapped BER parsing also hides the closure-backed wire parser, while leaving
//! the structural `BiMap` visible. This is deliberately narrower than hiding all
//! `Mapped` parsers or child formats. Scoped equality proofs in `parse` and
//! `lemma_serialize_len` likewise avoid exposing a whole schema to the solver.
//!
//! Implementation responsibilities are separated into four files:
//!
//! - `schema.rs`: inner constructors, retagging, and start-domain certificates.
//! - `proofs.rs`: opaque specifications and common / DER / BER proof traits.
//! - `exec.rs`: shared borrowed/owned executable delegation.
//! - `der_ord.rs`: shared borrowed/owned DER ordering delegation.
//!
//! This file only assembles those pieces. Internal helper macros are exported
//! because public macros must resolve them from other crates; they are not a
//! supported interface. Changes should be checked against the ASN.1 width,
//! depth, mixed-rule, and CMS fixtures, not just a primitive example.
mod der_ord;
mod exec;
mod proofs;
mod schema;

/// Implements the verified DER traits and executable APIs for a generated nominal format.
///
/// See [`asn1::macros`](crate::asn1::macros) for the required schema declarations,
/// invocation arguments, and examples.
#[macro_export]
macro_rules! impl_der {
    (
        $kind:ident($($argument:tt)*), borrowed,
        $fmt:ident, $inner:ty, $spec:ty, $value:ident $(, $forward:ty, $reverse:ty)?
    ) => {
        $crate::__impl_asn1_nominal_inner!($kind($($argument)*), $fmt, $inner);
        $crate::__impl_asn1_nominal_specs_and_proofs!($fmt, $spec);
        $crate::__impl_asn1_nominal_exec!(borrowed, $fmt, $value);
        $crate::__impl_asn1_nominal_der_ord!(
            borrowed, $fmt, $inner, $spec, $value $(, $forward, $reverse)?
        );
        $crate::__impl_asn1_nominal_tag_support!($kind($($argument)*), $fmt);
        $crate::impl_der!(
            @parser_proofs $kind($($argument)*), $fmt, $spec $(, $forward, $reverse)?
        );
    };
    (
        $kind:ident($($argument:tt)*), owned,
        $fmt:ident, $inner:ty, $spec:ty, $value:ty $(, $forward:ty, $reverse:ty)?
    ) => {
        $crate::__impl_asn1_nominal_inner!($kind($($argument)*), $fmt, $inner);
        $crate::__impl_asn1_nominal_specs_and_proofs!($fmt, $spec);
        $crate::__impl_asn1_nominal_exec!(owned, $fmt, $value);
        $crate::__impl_asn1_nominal_der_ord!(
            owned, $fmt, $inner, $spec, $value $(, $forward, $reverse)?
        );
        $crate::__impl_asn1_nominal_tag_support!($kind($($argument)*), $fmt);
        $crate::impl_der!(
            @parser_proofs $kind($($argument)*), $fmt, $spec $(, $forward, $reverse)?
        );
    };
    // Retagged DER formats may have an invalid expected tag. Establish their
    // inner invariants only after parsing succeeds; other formats need no guard.
    (@parser_proofs tag($form:ident), $fmt:ident, $spec:ty $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_der_tagged_proofs!($fmt, $spec $(, $forward, $reverse)?);
    };
    (@parser_proofs starts($domain:expr), $fmt:ident, $spec:ty $(, $forward:ty, $reverse:ty)?) => {
        $crate::__impl_asn1_nominal_der_fixed_proofs!($fmt, $spec $(, $forward, $reverse)?);
    };
}

/// Implements the verified BER traits and executable APIs for a generated nominal format.
///
/// BER formats deliberately do not implement `StrictParser`, `NonMalleable`, or DER ordering.
/// See [`asn1::macros`](crate::asn1::macros) for invocation arguments and examples.
#[macro_export]
macro_rules! impl_ber {
    (
        $kind:ident($($argument:tt)*), borrowed,
        $fmt:ident, $inner:ty, $spec:ty, $value:ident $(, $forward:ty, $reverse:ty)?
    ) => {
        $crate::__impl_asn1_nominal_inner!($kind($($argument)*), $fmt, $inner);
        $crate::__impl_asn1_nominal_specs_and_proofs!($fmt, $spec);
        $crate::__impl_asn1_nominal_exec!(borrowed, $fmt, $value $(, $forward, $reverse)?);
        $crate::__impl_asn1_nominal_ber_sound!($fmt, $spec $(, $forward, $reverse)?);
        $crate::__impl_asn1_nominal_tag_support!($kind($($argument)*), $fmt);
    };
    (
        $kind:ident($($argument:tt)*), owned,
        $fmt:ident, $inner:ty, $spec:ty, $value:ty $(, $forward:ty, $reverse:ty)?
    ) => {
        $crate::__impl_asn1_nominal_inner!($kind($($argument)*), $fmt, $inner);
        $crate::__impl_asn1_nominal_specs_and_proofs!($fmt, $spec);
        $crate::__impl_asn1_nominal_exec!(owned, $fmt, $value $(, $forward, $reverse)?);
        $crate::__impl_asn1_nominal_ber_sound!($fmt, $spec $(, $forward, $reverse)?);
        $crate::__impl_asn1_nominal_tag_support!($kind($($argument)*), $fmt);
    };
}

// Exported macros live at the crate root; also make them discoverable under asn1::macros.
pub use crate::{impl_ber, impl_der};
