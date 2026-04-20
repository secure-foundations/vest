use crate::core::{
    exec::{
        parser::{PResult, Parser},
        pred::Pred,
        ParseError,
    },
    spec::SpecParser,
};
use vstd::prelude::*;

verus! {

impl<I, A, PredFn> Parser<I> for super::Refined<A, PredFn> where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    PredFn: Pred<A::O>,
 {
    type O = A::O;

    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        let (n, v) = self.inner.parse(ibuf)?;
        if self.pred.test(&v) {
            Ok((n, v))
        } else {
            Err(ParseError::predicate_failed())
        }
    }
}

pub broadcast proof fn lemma_refined_exec_inv<I, A, PredFn>(fmt: &super::Refined<A, PredFn>)
    where
        I: View<V = Seq<u8>>,
        A: Parser<I>,
        PredFn: Pred<A::O>,
    requires
        fmt.inner.exec_inv(),
    ensures
        #[trigger] fmt.exec_inv(),
{
}

} // verus!
