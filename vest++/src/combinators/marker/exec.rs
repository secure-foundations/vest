use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, Compliance, Serializer},
};
use crate::Never;
use vstd::prelude::*;

verus! {

impl<I: View<V = Seq<u8>>> Parser<I> for super::Empty {
    type PT = ();

    fn parse(&self, _ibuf: &I) -> PResult<Self::PT> {
        Ok((0, ()))
    }
}

impl Serializer<()> for super::Empty {
    fn ex_serialize(&self, _v: (), _obuf: &mut Vec<u8>) {
    }
}

impl Compliance<()> for super::Empty {
    fn check_compliance(&self, _v: ()) -> (yes: bool) {
        true
    }
}

impl ByteLen<()> for super::Empty {
    fn length(&self, _v: ()) -> (len: usize) {
        0
    }
}

} // verus!
