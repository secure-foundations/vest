use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::regular::bytes::*;
use vest::regular::sequence::{Continuation, Pair, SpecPair};
use vest::regular::uints::*;
use vest::regular::*;
use vest::utils::*;
use vstd::prelude::*;

verus! {

pub open spec fn msg1() -> SpecPair<(BtcVarint, U24Be), (Variable, Variable)> {
    SpecPair { fst: (BtcVarint, U24Be), snd: |deps| msg1_snd(deps) }
}

pub open spec fn msg1_snd(deps: (VarInt, u24)) -> (Variable, Variable) {
    let (x, y) = deps;
    (Variable(x.spec_into()), Variable(y.spec_into()))
}

pub struct Msg1Cont;

impl Continuation<&(VarInt, u24)> for Msg1Cont {
    type Output = (Variable, Variable);

    open spec fn requires(&self, i: &(VarInt, u24)) -> bool {
        true
    }

    open spec fn ensures(&self, i: &(VarInt, u24), o: (Variable, Variable)) -> bool {
        o@ == msg1_snd(i@)
    }

    fn apply(&self, deps: &(VarInt, u24)) -> (Variable, Variable) {
        let (x, y) = *deps;
        (Variable(x.ex_into()), Variable(y.ex_into()))
    }
}

pub fn mk_msg1<'a>() -> (o: Pair<'a, &'a [u8], Vec<u8>, (BtcVarint, U24Be), (Variable, Variable), Msg1Cont>)
    ensures
        o@ == msg1(),
{
    Pair { fst: (BtcVarint, U24Be), snd: Msg1Cont, spec_snd: Ghost(|deps| msg1_snd(deps)) }
}

} // verus!
