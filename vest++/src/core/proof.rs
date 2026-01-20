use crate::core::spec::SpecParser;

use super::spec::*;
use vstd::prelude::*;

verus! {

/// Serialize-Parse roundtrip property: serializing then parsing recovers the original value
#[verusfmt::skip]
pub trait SPRoundTrip where
    Self: SpecByteLen +
          SpecParser<PVal = Self::T> +
          SpecSerializers<SVal = Self::T> +
          GoodSerializer +
          Unambiguity,
 {
    proof fn theorem_serialize_parse_roundtrip_internal(&self, v: Self::T, obuf: Seq<u8>)
        requires
            self.unambiguous(),
        ensures
            v.wf() ==> {
                let ibuf = self.spec_serialize_dps(v, obuf);
                let n = self.byte_len(v) as int;
                self.spec_parse(ibuf) == Some((n, v))
            },
    ;

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::T)
        requires
            self.unambiguous(),
        ensures
            v.wf() ==> {
                let bytes = self.spec_serialize(v);
                self.spec_parse(bytes) == Some((bytes.len() as int, v))
            },
    {
        let empty = Seq::<u8>::empty();
        self.theorem_serialize_parse_roundtrip_internal(v, empty);
        self.lemma_serialize_equiv(v, empty);
        self.lemma_serialize_len(v);
    }
}

/// Parse-Serialize roundtrip property: parsing then serializing preserves the input prefix
pub trait PSRoundTrip: SPRoundTrip + NonMalleable {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>)
        requires
            self.unambiguous(),
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> self.spec_serialize(v) == ibuf.take(n),
    {
        let c = self;
        if let Some((n, v)) = c.spec_parse(ibuf) {
            c.lemma_parse_wf(ibuf);
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
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        ensures
            self.spec_parse(buf1) matches Some((n1, v1)) ==> self.spec_parse(buf2) matches Some(
                (n2, v2),
            ) ==> v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
    ;
}

/// Combinators that implement both DPS and non-DPS serialization specs and
/// establish their equivalence
pub trait SpecSerializers: SpecSerializer + SpecSerializerDps<ST = Self::SVal> {
    /// Lemma: serializer equivalence between DPS and non-DPS specs
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>)
        ensures
            self.spec_serialize_dps(v, obuf) == self.spec_serialize(v) + obuf,
    ;
}

} // verus!
