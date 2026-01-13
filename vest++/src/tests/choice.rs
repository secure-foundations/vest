use crate::combinators::{Choice, Either, Refined, U8};
use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{
        GoodSerializer, Serializability, SpecCombinator, SpecParser, SpecSerializer,
        SpecSerializerDps, SpecType,
    },
};
use vstd::prelude::*;

verus! {

proof fn test_choice_compose() {
    let c = Choice(
        Choice(
            Refined { inner: U8, pred: |x: u8| x == 0u8 },
            Refined { inner: U8, pred: |x: u8| x == 2u8 },
        ),
        Refined { inner: U8, pred: |x: u8| x == 2u8 },
    );
    let obuf = Seq::empty();
    let v = Either::Left(Either::Right(2u8));
    // let v = Either::Right(seq![2u8]);
    assert(c.wf(v));
    assert(c.serializable(v, obuf));
    let ibuf = c.spec_serialize_dps(v, obuf);
    c.theorem_serialize_parse_roundtrip(v, obuf);
    assert(c.spec_parse(ibuf) == Some((1int, v)));
}

} // verus!
