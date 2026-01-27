use crate::combinators::{Eof, Opt, Optional, Refined, Tag, U16Le, U8};
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
    c.theorem_serialize_parse_roundtrip(v);
    assert(c.spec_parse(ibuf) == Some((2int, v)));
    // assert(c.spec_parse(ibuf) == Some((2int, v1)));
    // assert(c.spec_parse(ibuf) == Some((2int, v2)));
    // assert(c.spec_parse(ibuf) == Some((2int, v3)));
    // c.theorem_parse_serialize_roundtrip(ibuf, obuf);
}

proof fn test_chaining_end_with_eof() {
    #[verusfmt::skip]
    let c = Optional(Refined { inner: U8, pred: Pred2 },
            Optional(Refined { inner: U8, pred: Pred1 },
            Optional(Refined { inner: U8, pred: Pred3 },
            Eof)));
    assert(c.unambiguous());

    #[verusfmt::skip]
    let tag0 = Tag { inner: U16Le, tag: 0 };
    let tag1 = Tag { inner: U16Le, tag: 1 };
    let tag2 = Tag { inner: U16Le, tag: 2 };
    let d = Optional(tag0, Optional(tag1, Optional(tag2, Eof)));
    // U16Le.theorem_serialize_dps_parse_roundtrip(2, Seq::empty());
    // U16Le.theorem_serialize_dps_parse_roundtrip(0, Seq::empty());
    // U16Le.theorem_serialize_dps_parse_roundtrip(1, Seq::empty());
    assert forall|vb: (), obuf: Seq<u8>| vb.wf() implies parser_fails_on(
        tag0,
        #[trigger] tag1.spec_serialize_dps(vb, obuf),
    ) by {
        U16Le.theorem_serialize_dps_parse_roundtrip(tag1.tag, obuf);
    }
    assert forall|vb: (), obuf: Seq<u8>| vb.wf() implies parser_fails_on(
        tag0,
        #[trigger] tag2.spec_serialize_dps(vb, obuf),
    ) by {
        U16Le.theorem_serialize_dps_parse_roundtrip(tag2.tag, obuf);
    }
    assert forall|vb: (), obuf: Seq<u8>| vb.wf() implies parser_fails_on(
        tag1,
        #[trigger] tag2.spec_serialize_dps(vb, obuf),
    ) by {
        U16Le.theorem_serialize_dps_parse_roundtrip(tag2.tag, obuf);
    }
    assert(d.unambiguous());
}

} // verus!
