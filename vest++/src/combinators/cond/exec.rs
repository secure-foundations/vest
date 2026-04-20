use crate::core::{
    exec::{
        parser::{PResult, Parser},
        ParseError,
    },
    spec::SpecParser,
};
use vstd::prelude::*;

verus! {

impl<I, Inner> Parser<I> for super::Cond<Inner> where I: View<V = Seq<u8>>, Inner: Parser<I> {
    type O = Inner::O;

    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        if self.0 {
            self.1.parse(ibuf)
        } else {
            Err(ParseError::cond_rejected())
        }
    }
}

} // verus!
