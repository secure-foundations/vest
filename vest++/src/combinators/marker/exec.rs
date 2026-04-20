use crate::core::exec::parser::{PResult, Parser};
use crate::Never;
use vstd::prelude::*;

verus! {

impl<I: View<V = Seq<u8>>> Parser<I> for super::Empty {
    type O = ();

    fn parse(&self, _ibuf: &I) -> PResult<Self::O> {
        Ok((0, ()))
    }
}

} // verus!
