use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::regular::bytes::*;
use vest::regular::depend::SpecDepend;
use vest::regular::depend::{Continuation, Depend};
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;

verus! {

pub open spec fn msg1() -> SpecDepend<(BtcVarint, U24Be), (Bytes, Bytes)> {
    SpecDepend { fst: (BtcVarint, U24Be), snd: |deps| msg1_snd(deps) }
}

pub open spec fn msg1_snd(deps: (VarInt, u24)) -> (Bytes, Bytes) {
    let (x, y) = deps;
    (Bytes(x.spec_into()), Bytes(y.spec_into()))
}

pub struct Msg1PCont;
pub struct Msg1SCont;

impl Continuation<&(VarInt, u24)> for Msg1PCont {
    type Output = (Bytes, Bytes);

    open spec fn requires(&self, i: &(VarInt, u24)) -> bool {
        true
    }

    open spec fn ensures(&self, i: &(VarInt, u24), o: (Bytes, Bytes)) -> bool {
        o@ == msg1_snd(i@)
    }

    fn apply(&self, deps: &(VarInt, u24)) -> (Bytes, Bytes) {
        let (x, y) = *deps;
        (Bytes(x.ex_into()), Bytes(y.ex_into()))
    }
}

impl Continuation<(VarInt, u24)> for Msg1SCont {
    type Output = (Bytes, Bytes);

    open spec fn requires(&self, i: (VarInt, u24)) -> bool {
        true
    }

    open spec fn ensures(&self, i: (VarInt, u24), o: (Bytes, Bytes)) -> bool {
        o@ == msg1_snd(i@)
    }

    fn apply(&self, deps: (VarInt, u24)) -> (Bytes, Bytes) {
        let (x, y) = deps;
        (Bytes(x.ex_into()), Bytes(y.ex_into()))
    }
}

pub fn mk_msg1<'a>() -> (o: Depend<&'a [u8], Vec<u8>, (BtcVarint, U24Be), (Bytes, Bytes), Msg1PCont, Msg1SCont>)
    ensures
        o@ == msg1(),
{
    Depend { fst: (BtcVarint, U24Be), p_snd: Msg1PCont, s_snd: Msg1SCont, spec_snd: Ghost(|deps| msg1_snd(deps)) }
}

} // verus!
