use crate::core::exec::parser::{PResult, Parser};
use crate::Never;
use vstd::prelude::*;

verus! {

impl<I: View<V = Seq<u8>>> Parser<I> for super::Empty {
    type PT = ();

    fn parse(&self, _ibuf: &I) -> PResult<Self::PT> {
        Ok((0, ()))
    }
}

} // verus!
