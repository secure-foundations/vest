use crate::combinators::{Tail, U8};
use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{
        GoodSerializer, SpecCombinator, SpecParser, SpecSerializer, SpecSerializerDps, SpecType,
    },
};
use vstd::prelude::*;

verus! {

proof fn test_tail_compose() {
    let c = (U8, Tail);
    let obuf = Seq::empty();
    let v1 = (1u8, seq![3u8, 4u8, 5u8]);
    assert(c.wf(v1));
    assert(c.serializable(v1, obuf));
    let ibuf = c.spec_serialize_dps(v1, obuf);
    c.theorem_serialize_parse_roundtrip(v1, obuf);
    assert(c.spec_parse(ibuf) == Some((4int, v1)));

    let obuf_bad = seq![0u8; 1];
    assert(!c.serializable(v1, obuf_bad));

    let v2 = (seq![1u8, 2u8], 3u8);
    let c_bad = (Tail, U8);
    assert(c_bad.wf(v2));
    assert(!c_bad.serializable(v2, obuf));
}

} // verus!
