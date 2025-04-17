use modifier::Cond;
use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::errors::{ParseError, SerializeError};
use vest::properties::Combinator;
use vest::regular::bytes::*;
use vest::regular::sequence::{Continuation, Pair, SpecPair};
use vest::regular::uints::*;
use vest::regular::*;
use vest::utils::*;
use vstd::prelude::*;

use crate::my_vec;

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

pub fn mk_msg1() -> (o: Pair<(BtcVarint, U24Be), (VarInt, u24), (Variable, Variable), Msg1Cont>)
    ensures
        o@ == msg1(),
{
    Pair { fst: (BtcVarint, U24Be), snd: Msg1Cont, spec_snd: Ghost(|deps| msg1_snd(deps)) }
}

pub open spec fn msg2() -> SpecPair<bytes::Fixed<2>, Cond<U8>> {
    SpecPair { fst: bytes::Fixed::<2>, snd: |deps| msg2_snd(deps) }
}

pub open spec fn msg2_snd(deps: Seq<u8>) -> Cond<U8> {
    let bytes = deps;
    Cond {
        cond: bytes == seq![0u8, 1],
        inner: U8,
    }
}

pub struct Msg2Cont;

impl<'a> Continuation<&'a &[u8]> for Msg2Cont {
    type Output = Cond<U8>;

    open spec fn requires(&self, i: &'a &[u8]) -> bool {
        true
    }

    open spec fn ensures(&self, i: &'a &[u8], o: Cond<U8>) -> bool {
        o@ == msg2_snd(i@)
    }

    fn apply(&self, deps: &'a &[u8]) -> Cond<U8> {
        let bytes = deps;
        Cond {
            cond: bytes.compare(&[0, 1].as_slice()),
            inner: U8,
        }
    }
}

pub fn mk_msg2<'a>() -> (o: Pair<bytes::Fixed<2>, &'a[u8], Cond<U8>, Msg2Cont>)
    ensures
        o@ == msg2(),
{
    Pair {
        fst: bytes::Fixed::<2>,
        snd: Msg2Cont,
        spec_snd: Ghost(|deps| msg2_snd(deps)),
    }
}

fn test(buf: &[u8]) -> Result<(), SerializeError> {
    let msg2_combinator = mk_msg2();
    let mut outbuf: Vec<u8> = my_vec!(0, 0, 0, 0, 0, 0, 0, 0);
    let two_bytes = [0u8, 1];
    let two_bytes_ref = two_bytes.as_slice();
    let len = msg2_combinator.serialize((&two_bytes_ref, &0u8), &mut outbuf, 0)?;
    let res = <_ as Combinator<&[u8], Vec<u8>>>::parse(&msg2_combinator, buf);
    // if let Ok((len, val)) = msg2_combinator.parse(buf) {

    // }
    Ok(())
}

} // verus!
