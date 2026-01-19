use crate::combinators::{Opt, Optional, Refined, U8};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

struct Pred1;

struct Pred2;

struct Pred3;

impl SpecPred<u8> for Pred1 {
    open spec fn apply(&self, value: u8) -> bool {
        value == 1
    }
}

impl SpecPred<u8> for Pred2 {
    open spec fn apply(&self, value: u8) -> bool {
        value == 2
    }
}

impl SpecPred<u8> for Pred3 {
    open spec fn apply(&self, value: u8) -> bool {
        value == 3
    }
}

proof fn test_opt_compose() {
    let pred1 = |x: u8| x == 1u8;
    let pred2 = |x: u8| x == 2u8;
    let c = Optional(
        Refined { inner: U8, pred: Pred2 },
        Optional(Refined { inner: U8, pred: Pred1 }, Refined { inner: U8, pred: Pred3 }),
    );
    let obuf = seq![0u8; 10];
    // let v = ((Some(seq![2u8]), Some(seq![1u8])), Some(seq![2u8]));
    let v = (Some(Subset { val: 2u8, pred: Pred2 }), (None, Subset { val: 3u8, pred: Pred3 }));
    // let v = (Some(seq![0u8]), (Some(seq![1u8]), Some(seq![2u8])));
    // let v1 = (Some(seq![0u8]), (Some(seq![1u8]), None));
    // let v2 = (Some(seq![0u8]), (None, Some(seq![2u8])));
    // let v3 = (None, (Some(seq![1u8]), Some(seq![2u8])));
    assert(v.wf());
    assert(c.unambiguous());
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
