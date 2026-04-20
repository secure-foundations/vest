use crate::{
    combinators::Pair,
    core::{
        exec::{
            input::InputBuf,
            parser::{PResult, Parser},
        },
        spec::{SafeParser, SpecParser},
    },
};
use vstd::prelude::*;

verus! {

impl<I, A, B> Parser<I> for super::Terminated<A, B> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,
 {
    type O = A::O;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        let (n, (v, _)) = Pair(&self.0, &self.1).parse(ibuf)?;
        Ok((n, v))
    }
}

} // verus!
