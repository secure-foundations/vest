use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::regular::*;
use vest::regular::sequence::{SpecPair, Pair, Continuation};
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;

verus! {

pub open spec fn msg1() -> SpecPair<(BtcVarint, U24Be), (bytes::Variable, bytes::Variable)> {
    SpecPair { fst: (BtcVarint, U24Be), snd: |deps| msg1_snd(deps) }
}

pub open spec fn msg1_snd(deps: (VarInt, u24)) -> (bytes::Variable, bytes::Variable) {
    let (x, y) = deps;
    (bytes::Variable(x.spec_into()), bytes::Variable(y.spec_into()))
}

pub struct Msg1PCont;
pub struct Msg1SCont;

impl Continuation<&(VarInt, u24)> for Msg1Snd {
    type Output = (bytes::Variable, bytes::Variable);

    open spec fn requires(&self, i: &(VarInt, u24)) -> bool {
        true
    }

    open spec fn ensures(&self, i: &(VarInt, u24), o: (bytes::Variable, bytes::Variable)) -> bool {
        o@ == msg1_snd(i@)
    }

    fn apply(&self, deps: &(VarInt, u24)) -> (bytes::Variable, bytes::Variable) {
        let (x, y) = *deps;
        (bytes::Variable(x.ex_into()), bytes::Variable(y.ex_into()))
    }
}

pub fn mk_msg1<'a>() -> (o: Pair<&'a [u8], Vec<u8>, (BtcVarint, U24Be), (bytes::Variable, bytes::Variable), Msg1Snd>)
    ensures
        o@ == msg1(),
{
    Pair { fst: (BtcVarint, U24Be), snd: Msg1Snd, spec_snd: Ghost(|deps| msg1_snd(deps)) }
}

} // verus!
