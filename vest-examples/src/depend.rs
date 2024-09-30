use vest::regular::bytes::*;
use vest::regular::depend::SpecDepend;
use vest::regular::depend::{Continuation, Depend};
use vest::regular::uints::*;
use vstd::prelude::*;

verus! {

pub open spec fn msg1() -> SpecDepend<(U8, U16), (Bytes, Bytes)> {
    SpecDepend {
        fst: (U8, U16),
        snd: |deps| msg1_snd(deps),
    }
}

pub open spec fn msg1_snd(deps: (u8, u16)) -> (Bytes, Bytes)
{
    let (x, y) = deps;
    (Bytes(x as usize), Bytes(y as usize))
}

pub struct Msg1Snd;

impl Continuation<(u8, u16)> for Msg1Snd {
    type Output = (Bytes, Bytes);

    open spec fn requires(&self, i: (u8, u16)) -> bool {
        true
    }

    open spec fn ensures(&self, i: (u8, u16), o: (Bytes, Bytes)) -> bool {
        o@ == msg1_snd(i@)
    }

    fn apply(&self, deps: (u8, u16)) -> (Bytes, Bytes) {
        let (x, y) = deps;
        (Bytes(x as usize), Bytes(y as usize))
    }
}

pub fn mk_msg1() -> (o: Depend<
    (U8, U16),
    (Bytes, Bytes),
    Msg1Snd,
    >)
    ensures
        o@ == msg1(),
{
    Depend {
        fst: (U8, U16),
        snd: Msg1Snd,
        spec_snd: Ghost(|deps| msg1_snd(deps)),
    }
}

} // verus!
