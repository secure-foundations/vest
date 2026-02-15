use crate::core::spec::SpecParser;

use super::spec::*;
use vstd::prelude::*;

verus! {

/// Serialize-Parse roundtrip property: serializing (in DPS style) then parsing recovers the original value
///
/// ## Note
///
/// This trait is primarily used *internally* to achieve better composability of combinators.
/// See [`SPRoundTrip`] for the top-level, more user-friendly serialize-parse theorem.
#[verusfmt::skip]
pub trait SPRoundTripDps where
    Self: SpecByteLen +
          SpecParser<PVal = Self::T> +
          SpecSerializerDps<ST = Self::T> +
          Consistency<Val = Self::T> +
          Unambiguity,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>)
        requires
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

/// Serialize-Parse roundtrip property: serializing then parsing recovers the original value
///
/// ## Note
///
/// Technically, this theorem can be directly proved for individual combinators
/// if they only implement the necessary spec traits. However, we provide generic
/// proofs (aka blanket implementations) for combinators that already implement and prove
/// [`SPRoundTripDps`], [`GoodSerializer`], and [`EquivSerializers`].
#[verusfmt::skip]
pub trait SPRoundTrip where
    Self: SpecByteLen +
          SpecParser<PVal = Self::T> +
          SpecSerializer<SVal = Self::T> +
          Consistency<Val = Self::T> +
          Unambiguity,
{
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::T)
        requires
            self.unambiguous(),
            self.consistent(v),
        ensures
            ({
                let bytes = self.spec_serialize(v);
                self.spec_parse(bytes) == Some((bytes.len() as int, v))
            }),
    ;
}

// Prove [`SPRoundTrip`] once-and-for-all if the combinator already implements and
// proves [`GoodSerializer`] and [`EquivSerializers`]
impl<C: SPRoundTripDps + GoodSerializer + EquivSerializers> SPRoundTrip for C {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::T) {
        let empty = Seq::empty();
        self.theorem_serialize_dps_parse_roundtrip(v, empty);
        self.lemma_serialize_equiv_on_empty(v);
        self.lemma_serialize_len(v);
    }
}

/// Parse-Serialize roundtrip property: parsing then serializing preserves the input prefix
///
/// ## Note
///
/// Technically, this theorem can be directly proved for individual combinators
/// if they implement the necessary spec traits. However, we provide generic
/// proofs (aka blanket implementations) for combinators that already implement and prove
/// [`SPRoundTrip`] and [`NonMalleable`].
#[verusfmt::skip]
pub trait PSRoundTrip where
    Self: SpecByteLen +
          SpecParser<PVal = Self::T> +
          SpecSerializer<SVal = Self::T> +
          GoodParser +
          Unambiguity,
{
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>)
        requires
            self.inv(),
            self.unambiguous(),
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> self.spec_serialize(v) == ibuf.take(n),
    ;

    proof fn corollary_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        requires
            self.inv(),
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

// Prove [`PSRoundTrip`] once-and-for-all if the combinator already implements and
// proves [`SPRoundTrip`] and [`NonMalleable`]
impl<C: SPRoundTrip + NonMalleable> PSRoundTrip for C {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
        let c = self;
        if let Some((n, v)) = c.spec_parse(ibuf) {
            c.lemma_parse_consistent(ibuf);
            c.theorem_serialize_parse_roundtrip(v);

            let serialized = c.spec_serialize(v);
            assert((c.spec_parse(serialized)->0).1 == v);

            // By non-malleability: both parses return v, so serialized is equal to the input prefix
            c.lemma_parse_non_malleable(ibuf, serialized);
            assert(ibuf.take(n) == serialized);
        }
    }
}

/// Non-malleability property: equal parsed values imply equal input prefixes
pub trait NonMalleable: GoodParser {
    #[verusfmt::skip]
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        requires
            self.inv(),
        ensures
            self.spec_parse(buf1) matches Some((n1, v1)) ==>
            self.spec_parse(buf2) matches Some((n2, v2)) ==>
            v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
    ;
}

pub trait NoLookAhead: GoodParser + Unambiguity {
    #[verusfmt::skip]
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>)
        requires
            self.inv(),
            self.unambiguous(),
        ensures
            self.spec_parse(i1) matches Some((n, v)) ==>
            0 <= n <= i2.len() ==> i2.take(n) == i1.take(n) ==>
            self.spec_parse(i2) == Some((n, v)),
    ;

    proof fn corollary_non_extensible(&self, i1: Seq<u8>, i2: Seq<u8>)
        requires
            self.inv(),
            self.unambiguous(),
        ensures
            self.spec_parse(i1) matches Some((n, v)) ==> self.spec_parse(i1 + i2) == Some((n, v)),
    {
        self.lemma_no_lookahead(i1, i1 + i2);
        if let Some((n, v)) = self.spec_parse(i1) {
            self.lemma_parse_len_bound(i1);
            assert(0 <= n <= (i1 + i2).len());
            assert(i1.take(n) == (i1 + i2).take(n));
        }
    }
}

/// Combinators that implement both DPS and non-DPS serialization specs and
/// establish their equivalence
pub trait EquivSerializersGeneral: SpecSerializer + SpecSerializerDps<ST = Self::SVal> {
    /// Lemma: serializer equivalence between DPS and non-DPS specs
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>)
        ensures
            self.spec_serialize_dps(v, obuf) == self.spec_serialize(v) + obuf,
    ;
}

pub trait EquivSerializers: SpecSerializer + SpecSerializerDps<ST = Self::SVal> {
    /// Lemma: serializer equivalence between DPS and non-DPS specs
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal)
        ensures
            self.spec_serialize_dps(v, seq![]) == self.spec_serialize(v),
    ;
}

} // verus!

pub use crate::core::fns::{
    EquivSerializersGeneralSpecs, EquivSerializersSpecs, NonMalleableSpecs, PSRoundTripSpecs,
    SPRoundTripDpsSpecs, SPRoundTripSpecs, WfEquivSerializers, WfEquivSerializersGeneral,
    WfNonMalleable, WfPSRoundTrip, WfSPRoundTrip, WfSPRoundTripDps,
};
