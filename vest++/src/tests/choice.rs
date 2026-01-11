use crate::combinators::{Choice, Either, Fixed, Refined};
use crate::core::{
    proof::{NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{SpecCombinator, SpecParser, SpecSerializer, SpecSerializerDps, SpecType},
};
use vstd::prelude::*;

verus! {

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

} // verus!
