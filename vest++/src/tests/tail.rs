use crate::combinators::{Fixed, Tail};
use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{
        GoodSerializer, SpecCombinator, SpecParser, SpecSerializer, SpecSerializerDps, SpecType,
    },
};
use vstd::prelude::*;

verus! {

proof fn test_tail_compose() {
    let c = (Fixed::<2>, Tail);
    let obuf = Seq::empty();
    let v = (seq![1u8, 2u8], seq![3u8, 4u8, 5u8]);
    assert(c.wf(v));
    assert(c.serializable(v, obuf));
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v, obuf);
    assert(c.spec_parse(ibuf) == Some((5int, v)));

    let obuf_bad = seq![0u8; 1];
    assert(!c.serializable(v, obuf_bad));

    let c_bad = (Tail, Fixed::<3>);
    assert(c_bad.wf(v));
    assert(!c_bad.serializable(v, obuf));
}

} // verus!
