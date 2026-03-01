//! Correctness and security proof traits for Vest++ combinators.

use crate::core::spec::SpecParser;

use super::spec::*;
use vstd::prelude::*;

verus! {

/// Serialize-parse roundtrip (DPS).
///
/// Serializing a consistent value in DPS style and parsing the result recovers the
/// original value, consuming exactly `byte_len(v)` bytes.
///
/// This is a low-level trait. Individual combinators in the library prove this directly;
/// the higher-level property [`SPRoundTrip`] is derived via a blanket impl composing this with
/// [`GoodSerializer`] and [`EquivSerializers`].
///
/// ## Note on user-defined combinators
///
/// User-defined combinators should prefer proving this trait to proving [`SPRoundTrip`], as
/// 1. it's a stronger property and proving and implementing this trait would make Rust/Verus auto-derive a proof for [`SPRoundTrip`];
/// 2. it makes the combinator composable with the rest of the library, which are all built on this stronger property.
pub trait SPRoundTripDps where
    Self: SpecByteLen +
          SpecParser<PVal = Self::T> +
          SpecSerializerDps<ST = Self::T> +
          Consistency<Val = Self::T> +
          Unambiguity,
 {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        true
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>)
        requires
            self.sp_roundtrip_dps_inv(),
            self.unambiguous(),
            self.consistent(v),
        ensures
            ({
                let ibuf = self.spec_serialize_dps(v, obuf);
                let n = self.byte_len(v) as int;
                self.spec_parse(ibuf) == Some((n, v))
            }),
    ;
}

/// Serialize-parse roundtrip.
///
/// Serializing a consistent value and parsing the result recovers `v`, consuming
/// the entire serialized buffer. Automatically derived for combinators implementing
/// [`SPRoundTripDps`] + [`GoodSerializer`] + [`EquivSerializers`].
///
/// ## Note on user-defined combinators
///
/// User-defined combinators should prefer proving [`SPRoundTripDps`] to proving this trait. See the note on [`SPRoundTripDps`] for details.
pub trait SPRoundTrip where
    Self: SpecByteLen +
          SpecParser<PVal = Self::T> +
          SpecSerializer<SVal = Self::T> +
          Consistency<Val = Self::T> +
          Unambiguity,
{
    open spec fn sp_roundtrip_inv(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::T)
        requires
            self.sp_roundtrip_inv(),
            self.unambiguous(),
            self.consistent(v),
        ensures
            ({
                let bytes = self.spec_serialize(v);
                self.spec_parse(bytes) == Some((bytes.len() as int, v))
            }),
    ;
}

impl<C: SPRoundTripDps + GoodSerializer + EquivSerializers> SPRoundTrip for C {
    open spec fn sp_roundtrip_inv(&self) -> bool {
        self.serialize_inv() && self.sp_roundtrip_dps_inv()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::T) {
        let empty = Seq::empty();
        self.theorem_serialize_dps_parse_roundtrip(v, empty);
        self.lemma_serialize_equiv_on_empty(v);
        self.lemma_serialize_len(v);
    }
}

/// Parse-serialize roundtrip.
///
/// Parsing a buffer and serializing the result reproduces the consumed bytes.
///
/// Automatically derived for combinators implementing [`SPRoundTrip`] + [`NonMalleable`].
///
/// User-defined combinators can also prove this directly.
pub trait PSRoundTrip where
    Self: SpecByteLen +
          SpecParser<PVal = Self::T> +
          SpecSerializer<SVal = Self::T> +
          Unambiguity,
{
    open spec fn ps_roundtrip_inv(&self) -> bool {
        true
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>)
        requires
            self.ps_roundtrip_inv(),
            self.unambiguous(),
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> self.spec_serialize(v) == ibuf.take(n),
    ;

    proof fn corollary_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        requires
            self.ps_roundtrip_inv(),
            self.unambiguous(),
        ensures
            self.spec_parse(buf1) matches Some((n1, v1)) ==>
            self.spec_parse(buf2) matches Some((n2, v2)) ==>
            v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
    {
        self.theorem_parse_serialize_roundtrip(buf1);
        self.theorem_parse_serialize_roundtrip(buf2);
    }
}

impl<C: SPRoundTrip + NonMalleable> PSRoundTrip for C {
    open spec fn ps_roundtrip_inv(&self) -> bool {
        self.sound_inv() && self.nonmal_inv() && self.sp_roundtrip_inv()
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
        let c = self;
        if let Some((n, v)) = c.spec_parse(ibuf) {
            c.lemma_parse_sound_value(ibuf);
            c.theorem_serialize_parse_roundtrip(v);

            let serialized = c.spec_serialize(v);
            assert((c.spec_parse(serialized)->0).1 == v);

            // By non-malleability: both parses return v, so serialized is equal to the input prefix
            c.lemma_parse_non_malleable(ibuf, serialized);
            assert(ibuf.take(n) == serialized);
        }
    }
}

/// Parser non-malleability.
///
/// If two buffers parse to equal values, their consumed bytes are identical—i.e.,
/// each semantic value has a unique byte-level representation.
pub trait NonMalleable: SoundParser {
    /// Optional invariant (used by spec-function combinators; struct-based combinators
    /// typically leave this as `true`)
    open spec fn nonmal_inv(&self) -> bool {
        true
    }

    #[verusfmt::skip]
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        requires
            self.sound_inv(),
            self.nonmal_inv(),
        ensures
            self.spec_parse(buf1) matches Some((n1, v1)) ==>
            self.spec_parse(buf2) matches Some((n2, v2)) ==>
            v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
    ;
}

/// No-lookahead property for parsers.
///
/// Intuitively: the parser's behavior does not depend on "future" bytes beyond the consumed prefix
/// (i.e., it does not need to "look ahead"/"peek" at them to decide how to parse the prefix).
///
/// Formally: if two buffers share a common prefix that successfully parses, then they parse to the same value.
pub trait NoLookAhead: SoundParser + Unambiguity {
    #[verusfmt::skip]
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>)
        requires
            self.sound_inv(),
            self.unambiguous(),
        ensures
            self.spec_parse(i1) matches Some((n, v)) ==>
            0 <= n <= i2.len() ==> i2.take(n) == i1.take(n) ==>
            self.spec_parse(i2) == Some((n, v)),
    ;

    proof fn corollary_non_extensible(&self, i1: Seq<u8>, i2: Seq<u8>)
        requires
            self.sound_inv(),
            self.unambiguous(),
        ensures
            self.spec_parse(i1) matches Some((n, v)) ==> self.spec_parse(i1 + i2) == Some((n, v)),
    {
        self.lemma_no_lookahead(i1, i1 + i2);
        if let Some((n, v)) = self.spec_parse(i1) {
            self.lemma_parse_safe(i1);
            assert(0 <= n <= (i1 + i2).len());
            assert(i1.take(n) == (i1 + i2).take(n));
        }
    }
}

/// Full DPS ↔ non-DPS serializer equivalence for *any* output buffer.
///
/// See [`EquivSerializers`] for the weaker empty-buffer variant.
pub trait EquivSerializersGeneral: SpecSerializer + SpecSerializerDps<ST = Self::SVal> {
    /// `spec_serialize_dps(v, obuf) == spec_serialize(v) + obuf`.
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>)
        ensures
            self.spec_serialize_dps(v, obuf) == self.spec_serialize(v) + obuf,
    ;
}

/// DPS ↔ non-DPS serializer equivalence on the empty buffer.
///
/// Sufficient for deriving [`SPRoundTrip`] from [`SPRoundTripDps`].
pub trait EquivSerializers: SpecSerializer + SpecSerializerDps<ST = Self::SVal> {
    /// `spec_serialize_dps(v, []) == spec_serialize(v)`.
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal)
        ensures
            self.spec_serialize_dps(v, seq![]) == self.spec_serialize(v),
    ;
}

} // verus!
