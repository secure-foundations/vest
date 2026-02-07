use crate::combinators::{Tail, U8};
use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip, SPRoundTripDps},
    spec::{
        GoodSerializer, Serializability, SpecCombinator, SpecParser, SpecSerializer,
        SpecSerializerDps, Unambiguity,
    },
};
use vstd::prelude::*;

verus! {

proof fn test_tail_compose() {
    let c = (U8, Tail);
    let obuf = Seq::empty();
    let v1 = (1u8, seq![3u8, 4u8, 5u8]);
    assert(c.unambiguous());
    let ibuf = c.spec_serialize_dps(v1, obuf);
    c.theorem_serialize_parse_roundtrip(v1);
    assert(c.spec_parse(ibuf) == Some((4int, v1)));
}

proof fn test_tail_ill_composed() {
    let c = (Tail, U8);
    let obuf = Seq::<u8>::empty();
    let v1 = (seq![3u8, 4u8, 5u8], 1u8);
    // the following line fails to compile, which is what we want
    // c.theorem_serialize_dps_parse_roundtrip(v1, obuf);
}

} // verus!
