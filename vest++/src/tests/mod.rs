#[allow(unused_imports)]
use crate::combinators::{Choice, Either, Fixed, Opt, Refined, Tail};
#[allow(unused_imports)]
use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{SpecCombinator, SpecParser, SpecSerializer, SpecType},
};
use vstd::prelude::*;

verus! {

proof fn test_opt_compose() {
    let c = (
        (
            Opt(Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 2u8 }),
            Opt(Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 1u8 }),
        ),
        Opt(Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 2u8 }),
    );
    let obuf = seq![0u8; 10];
    // let v = ((Some(seq![2u8]), Some(seq![1u8])), Some(seq![2u8]));
    let v = ((Some(seq![2u8]), None), Some(seq![2u8]));
    // let v = (Some(seq![0u8]), (Some(seq![1u8]), Some(seq![2u8])));
    // let v1 = (Some(seq![0u8]), (Some(seq![1u8]), None));
    // let v2 = (Some(seq![0u8]), (None, Some(seq![2u8])));
    // let v3 = (None, (Some(seq![1u8]), Some(seq![2u8])));
    assert(c.wf(v));
    assert(c.serializable(v, obuf));
    // assert(c.wf(v1));
    // assert(c.wf(v2));
    // assert(c.wf(v3));
    let ibuf = c.spec_serialize_dps(v, obuf);
    // let ibuf = c.spec_serialize(v1, obuf);
    // let ibuf = c.spec_serialize(v2, obuf);
    // let ibuf = c.spec_serialize(v3, obuf);
    c.theorem_serialize_parse_roundtrip(v, obuf);
    assert(c.spec_parse(ibuf) == Some((2int, v)));
    // assert(c.spec_parse(ibuf) == Some((2int, v1)));
    // assert(c.spec_parse(ibuf) == Some((2int, v2)));
    // assert(c.spec_parse(ibuf) == Some((2int, v3)));
    // c.theorem_parse_serialize_roundtrip(ibuf, obuf);
}

proof fn test_choice_compose() {
    let c = Choice(
        Choice(
            Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 0u8 },
            Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 2u8 },
        ),
        Refined { inner: Fixed::<1>, pred: |x: Seq<u8>| x[0] == 2u8 },
    );
    let obuf = Seq::empty();
    let v = Either::Left(Either::Right(seq![2u8]));
    // let v = Either::Right(seq![2u8]);
    assert(c.wf(v));
    assert(c.serializable(v, obuf));
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v, obuf);
    assert(c.spec_parse(ibuf) == Some((1int, v)));
}

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
