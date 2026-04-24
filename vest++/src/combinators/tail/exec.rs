use crate::core::exec::{
    input::InputBuf,
    parser::{PResult, Parser},
    ParseError,
};
use vstd::prelude::*;

verus! {

impl<I: InputBuf> Parser<I> for super::Tail {
    type O = I;

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        let len = ibuf.len();
        let tail = ibuf.take(len);
        proof {
            assert(tail.deep_view() == ibuf@);
        }
        Ok((len, tail))
    }
}

impl<I: InputBuf> Parser<I> for super::Eof {
    type O = ();

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        let len = ibuf.len();
        if len == 0 {
            Ok((0, ()))
        } else {
            Err(ParseError::expecting_eof())
        }
    }
}

} // verus!
