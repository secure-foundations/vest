use crate::combinators::AsLen;
use crate::core::exec::input::InputBuf;
use crate::core::exec::{
    parser::{PResult, Parser},
    ParseError,
};
use crate::core::spec::SpecParser;
use vstd::prelude::*;

verus! {

impl<const N: usize, I: InputBuf> Parser<I> for super::Fixed<N> {
    type O = I;

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        if ibuf.len() < N {
            Err(ParseError::unexpected_eof())
        } else {
            Ok((N, ibuf.take(N)))
        }
    }
}

impl<Len: AsLen, I: InputBuf> Parser<I> for super::Varied<Len> {
    type O = I;

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        let len = self.0.as_usize();
        if ibuf.len() < len {
            Err(ParseError::unexpected_eof())
        } else {
            Ok((len, ibuf.take(len)))
        }
    }
}

impl<I, Len, Inner> Parser<I> for super::ExactLen<Inner, Len> where
    I: InputBuf,
    Len: AsLen,
    Inner: Parser<I, PVal = Seq<u8>>,
 {
    type O = Inner::O;

    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        super::AndThen(super::Varied(self.0), &self.1).parse(ibuf)
    }
}

impl<I: InputBuf, A, Then> Parser<I> for super::AndThen<A, Then> where
    A: Parser<I, O = I, PVal = Seq<u8>>,
    Then: Parser<I>,
 {
    type O = Then::O;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        assert(self.exec_inv());

        let (len_a, chunk) = self.0.parse(ibuf)?;
        proof {
            chunk.deep_view_eq_view();
        }
        let (len_b, v) = self.1.parse(&chunk)?;
        if len_b == len_a {
            Ok((len_b, v))
        } else {
            Err(ParseError::length_mismatch())
        }
    }
}

} // verus!
