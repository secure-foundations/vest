use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl SPRoundTripDps for super::BerBool {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let serialized = self.spec_serialize_dps(v, obuf);
        let n = self.byte_len(v) as int;
        assert(self.byte_len(v) == v.blen());
        assert(n == 1int);

        if v {
            // Prove that there exists at least one non-zero byte (trigger)
            assert(super::spec::non_zero_byte(0x01u8));

            let n = choose|x: u8| super::spec::non_zero_byte(x);
            assert(super::spec::non_zero_byte(n));
            assert(n != 0u8);

            assert(self.spec_parse(serialized) == Some((1int, true)));
        } else {
        }
        assert(self.spec_parse(serialized) == Some((n, v)));
    }
}

impl EquivSerializersGeneral for super::BerBool {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
    }
}

impl EquivSerializers for super::BerBool {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
    }
}

// BerBool does NOT implement PSRoundTrip because it's malleable
// BerBool does NOT implement NonMalleable
// Example: seq![0xFF] and seq![0x01] both parse to true, but the prefixes differ
} // verus!
