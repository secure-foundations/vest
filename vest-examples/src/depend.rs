use vest::regular::bytes::*;
use vest::regular::depend::SpecDepend;
use vest::regular::depend::{Continuation, Depend};
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;

verus! {

pub open spec fn msg1() -> SpecDepend<(U8, U24Be), (Bytes, Bytes)> {
    SpecDepend { fst: (U8, U24Be), snd: |deps| msg1_snd(deps) }
}

pub open spec fn msg1_snd(deps: (u8, u24)) -> (Bytes, Bytes) {
    let (x, y) = deps;
    (Bytes(x.spec_into()), Bytes(y.spec_into()))
}

pub struct Msg1Snd;

impl Continuation<(u8, u24)> for Msg1Snd {
    type Output = (Bytes, Bytes);

    open spec fn requires(&self, i: (u8, u24)) -> bool {
        true
    }

    open spec fn ensures(&self, i: (u8, u24), o: (Bytes, Bytes)) -> bool {
        o@ == msg1_snd(i@)
    }

    fn apply(&self, deps: (u8, u24)) -> (Bytes, Bytes) {
        let (x, y) = deps;
        (Bytes(x.ex_into()), Bytes(y.ex_into()))
    }
}

pub fn mk_msg1() -> (o: Depend<'static, (U8, U24Be), (Bytes, Bytes), Msg1Snd>)
    ensures
        o@ == msg1(),
{
    Depend { fst: (U8, U24Be), snd: Msg1Snd, spec_snd: Ghost(|deps| msg1_snd(deps)) }
}

} // verus!
