use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::Serializer,
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
    fn ex_serialize(&self, _v: &(), _obuf: &mut Vec<u8>) {
    }
}

} // verus!
