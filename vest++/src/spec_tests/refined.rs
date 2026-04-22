use crate::combinators::{refined::exec::lemma_refined_exec_inv, Refined, U8};
use crate::core::exec::parser::Parser;
use crate::core::exec::fns::{FnPred, Pred};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

#[verifier::allow_in_spec]
pub fn small_nonzero(value: &u8) -> bool
    returns
        *value != 0u8,
{
    *value != 0u8
}

struct SmallNonZero;

impl SpecPred<u8> for SmallNonZero {
    open spec fn apply(&self, value: u8) -> bool {
        small_nonzero(&value)
    }
}

impl Pred<u8> for SmallNonZero {
    fn test(&self, value: &u8) -> (ok: bool) {
        small_nonzero(value)
    }
}

proof fn test_refined_pred_roundtrip() {
    let fmt = Refined { inner: U8, pred: SmallNonZero };

    assert(fmt.unambiguous());
    assert(fmt.consistent(5u8));
    assert(!fmt.consistent(0u8));

    fmt.theorem_serialize_parse_roundtrip(5u8);

    let ibuf = fmt.spec_serialize(5u8);
    assert(fmt.spec_parse(ibuf) == Some((1int, 5u8)));
    assert(fmt.spec_parse(seq![0u8]) is None);
}

fn test_refined_pred_exec(ibuf: &[u8]) {
    let fmt = Refined { inner: U8, pred: SmallNonZero };
    let magic = 11u8;
    let fmt2 = Refined {
        inner: U8,
        // pred: FnPred::<_, _, PredFnSpec<u8>>::new(small_nonzero, Ghost(|v| small_nonzero(&v))),
        pred: FnPred::<_, _, PredFnSpec<u8>>::new(
            |v| -> (ok: bool)
                ensures
                    ok == (*v != magic),
                { *v != magic },
            Ghost(|v| v != magic),
        ),
    };

    proof {
        lemma_refined_exec_inv::<&[u8], _, _>(&fmt2);
    }

    let _ = fmt.parse(&ibuf);
    let _ = fmt2.parse(&ibuf);
}

} // verus!
