use crate::core::spec::SpecParser;

use super::spec::*;
use vstd::prelude::*;

verus! {

/// Serialize-Parse roundtrip property: serializing then parsing recovers the original value
pub trait SPRoundTrip: SpecParser + SpecSerializerDps + Unambiguity<ST = Self::PT> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::ST, obuf: Seq<u8>)
        requires
            self.unambiguous(),
        ensures
            v.wf() ==> {
                let ibuf = self.spec_serialize_dps(v, obuf);
                let n = ibuf.len() - obuf.len();
                self.spec_parse(ibuf) == Some((n, v))
            },
    ;
}

/// Parse-Serialize roundtrip property: parsing then serializing preserves the input prefix
pub trait PSRoundTrip: SPRoundTrip + NonMalleable {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>)
        requires
            self.unambiguous(),
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> self.spec_serialize_dps(v, seq![])
                == ibuf.take(n),
    {
        let c = self;
        let empty = Seq::<u8>::empty();
        if let Some((n, v)) = c.spec_parse(ibuf) {
            c.lemma_parse_length(ibuf);
            c.lemma_parse_wf(ibuf);
            c.theorem_serialize_parse_roundtrip(v, empty);

            let serialized = c.spec_serialize_dps(v, empty);
            let n2 = serialized.len() as int;
            assert(c.spec_parse(serialized) == Some((n2, v)));

            // By non-malleability: both parses return v, so prefixes are equal
            c.lemma_parse_non_malleable(ibuf, serialized);
            assert(ibuf.take(n) == serialized.take(n2));
            assert(ibuf.take(n) == serialized);
        }
    }
}

/// Non-malleability property: equal parsed values imply equal input prefixes
pub trait NonMalleable: GoodParser {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        ensures
            self.spec_parse(buf1) matches Some((n1, v1)) ==> self.spec_parse(buf2) matches Some(
                (n2, v2),
            ) ==> v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
    ;
}

/// Deterministic serializer property: DPS and non-DPS serialization are equivalent
///
/// ## Note
/// Verus `spec` functions are *always* deterministic, even if they involve the hilbert choice operator
/// `choose` (which makes arbitrary but fixed choices for the same predicate).
/// Hence, we model non-deterministic serializers by relating two different serializer
/// specs (DPS and non-DPS), since a deterministic serializer would produce
/// identical outputs regardless of the serialization strategy.
pub trait Deterministic: SpecSerializer + SpecSerializerDps<ST = <Self as SpecSerializer>::ST> {
    /// Lemma: serializer equivalence between DPS and non-DPS specs
    proof fn lemma_serialize_equiv(&self, v: <Self as SpecSerializer>::ST, obuf: Seq<u8>)
        ensures
            self.spec_serialize_dps(v, obuf) == self.spec_serialize(v) + obuf,
    ;
}

/// Combined trait for all proof properties (for backward compatibility)
pub trait SpecCombinatorProof: GoodCombinator + SPRoundTrip + PSRoundTrip + NonMalleable {

}

// Blanket implementation: any type implementing all three traits automatically implements SpecCombinatorProof
impl<T: GoodCombinator + SPRoundTrip + PSRoundTrip + NonMalleable> SpecCombinatorProof for T {

}

// /// Serializability property: parsed values are serializable for some output buffer
// pub trait Serializable: PSRoundTrip {
//     /// Lemma: parser returns serializable values
//     ///
//     /// NOTE: This might not be true for all combinators, e.g., for [`Choice`](crate::combinators::choice::Choice)
//     ///
//     /// ```rust
//     /// impl<A: Serializable, B: Serializable> Serializable for super::Choice<A, B> {
//     ///     proof fn lemma_parse_serializable(&self, ibuf: Seq<u8>) {
//     ///         if let Some((n, v)) = self.spec_parse(ibuf) {
//     ///             match v {
//     ///                 Either::Left(va) => {
//     ///                     self.0.lemma_parse_serializable(ibuf);
//     ///                     let wit = choose|obuf: Seq<u8>| self.0.serializable(va, obuf);
//     ///                     assert(self.serializable(Either::Left(va), wit));
//     ///                 },
//     ///                 Either::Right(vb) => {
//     ///                     self.1.lemma_parse_serializable(ibuf);
//     ///                     let wit = choose|obuf: Seq<u8>| self.1.serializable(vb, obuf);
//     ///                     self.1.theorem_parse_serialize_roundtrip(ibuf, wit);
//     ///                     let obuf = self.1.spec_serialize_dps(vb, wit);
//     ///                     assert(ibuf.take(n) + wit == obuf);
//     ///                     assert(self.0.spec_parse(ibuf) is None);
//     ///                     assume(self.0.spec_parse(obuf) is None);
//     ///                     assert(self.serializable(Either::Right(vb), wit));
//     ///                 },
//     ///             }
//     ///         }
//     ///     }
//     /// }
//     /// ```
//     proof fn lemma_parse_serializable(&self, ibuf: Seq<u8>)
//         ensures
//             self.spec_parse(ibuf) matches Some((n, v)) ==> exists|obuf| self.serializable(v, obuf),
//     ;
// }
} // verus!
