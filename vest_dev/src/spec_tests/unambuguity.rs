use crate::combinators::tuple::Pair;
use crate::combinators::{Choice, Const, Optional, Refined, Sum, U8};
use crate::core::{proof::*, spec::*};

use vstd::prelude::*;
verus! {

struct Pred0;

struct Pred1;

impl SpecPred<u8> for Pred0 {
    open spec fn apply(&self, value: u8) -> bool {
        value == 0
    }
}

impl SpecPred<u8> for Pred1 {
    open spec fn apply(&self, value: u8) -> bool {
        value == 1
    }
}

proof fn test() {
    use crate::core::spec::*;
    let pred0 = |v: u8| v == 0;
    let pred1 = |v: u8| v == 1;
    let opt = Optional(Refined(U8, pred0), Refined(U8, pred1));
    let opt2 = Optional(Refined(U8, Pred0), Refined(U8, Pred1));
    let choice1 = Choice(Const(U8, 0), Choice(Const(U8, 1), Pair(Const(U8, 10), U8)));
    // assert forall|vb: Subset<u8, PredFnSpec<u8>>, va: Subset<u8, PredFnSpec<u8>>| #![auto] mutual_exclusive(vb, va) by {}
    // assert forall|vb: Subset<u8, Pred0>, va: Subset<u8, Pred1>| #![auto] va.wf() implies !vb.wf() by {}

    // assert forall|vb: Subset<u8, Pred1>, obuf: Seq<u8>| #![auto] vb.wf() implies opt2.0.fails_to_parse(opt2.1.spec_serialize_dps(vb, obuf)) by {
    //     if vb.wf() {
    //         assert(vb.val == 1);
    //     }
    // }
    // assert(opt.unambiguous());
    assert(opt2.unambiguous());
    assert(choice1.unambiguous());
}

} // verus!
