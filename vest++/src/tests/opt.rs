use crate::combinators::{Opt, Refined, U8};
use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{
        GoodSerializer, Serializability, SpecCombinator, SpecParser, SpecSerializer,
        SpecSerializerDps, SpecType,
    },
};
use vstd::prelude::*;

verus! {

proof fn test_opt_compose() {
    let c = (
        (
            Opt(Refined { inner: U8, pred: |x: u8| x == 2u8 }),
            Opt(Refined { inner: U8, pred: |x: u8| x == 1u8 }),
        ),
        Opt(Refined { inner: U8, pred: |x: u8| x == 2u8 }),
    );
    let obuf = seq![0u8; 10];
    // let v = ((Some(seq![2u8]), Some(seq![1u8])), Some(seq![2u8]));
    let v = ((Some(2u8), None), Some(2u8));
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

} // verus!
