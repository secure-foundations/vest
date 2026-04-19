use crate::combinators::AsLen;
use crate::core::exec::input::InputBuf;
use crate::core::exec::input::InputSlice;
use crate::core::exec::{
    parser::{PResult, Parser},
    ParseError,
};
use crate::core::spec::SpecParser;
use vstd::prelude::*;

verus! {

impl<const N: usize, I: InputBuf> Parser<I, I::Slice> for super::Fixed<N> {
    fn parse(&self, ibuf: &I) -> PResult<I::Slice> {
        if ibuf.len() < N {
            Err(ParseError::unexpected_eof())
        } else {
            Ok((N, ibuf.take(N)))
        }
    }
}

impl<Len: AsLen, I: InputBuf> Parser<I, I::Slice> for super::Varied<Len> {
    fn parse(&self, ibuf: &I) -> PResult<I::Slice> {
        let len = self.0.as_usize();
        if ibuf.len() < len {
            Err(ParseError::unexpected_eof())
        } else {
            Ok((len, ibuf.take(len)))
        }
    }
}

impl<I, Len, Inner, InnerT> Parser<I, InnerT> for super::ExactLen<Inner, Len> where
    I: InputBuf,
    Len: AsLen,
    Inner: Parser<I::Slice, InnerT, PVal = Seq<u8>>,
    InnerT: DeepView<V = Inner::PVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<InnerT> {
        super::AndThen(super::Varied(self.0), &self.1).parse(ibuf)
    }
}

impl<I: InputBuf, A, Then, ThenT> Parser<I, ThenT> for super::AndThen<A, Then> where
    A: Parser<I, I::Slice, PVal = Seq<u8>>,
    Then: Parser<I::Slice, ThenT>,
    ThenT: DeepView<V = Then::PVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<ThenT> {
        assert(self.exec_inv());
        match self.0.parse(ibuf) {
            Err(e) => Err(e),
            Ok((len_a, chunk)) => {
                proof {
                    chunk.deep_view_eq_view();
                }
                match self.1.parse(&chunk) {
                    Ok((len_b, v)) => if len_b == len_a {
                        Ok((len_b, v))
                    } else {
                        Err(ParseError::length_mismatch())
                    },
                    Err(e) => Err(e),
                }
            },
        }
    }
}

} // verus!
