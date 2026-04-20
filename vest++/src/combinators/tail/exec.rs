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
        Ok((len, ibuf.take(len)))
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
