use crate::core::{
    exec::{
        input::InputBuf,
        parser::{PResult, Parser},
    },
    spec::{SafeParser, SpecParser},
};
use vstd::prelude::*;

verus! {

impl<I, A> Parser<I> for super::Opt<A> where I: View<V = Seq<u8>>, A: Parser<I> {
    type O = Option<A::O>;

    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        match self.0.parse(ibuf) {
            Ok((n, v)) => Ok((n, Some(v))),
            Err(_) => {
                let none = None;
                assert(self.spec_parse(ibuf@) == Some((0int, none.deep_view())));
                Ok((0, none))
            },
        }
    }
}

impl<I, A, B> Parser<I> for super::Optional<A, B> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,
 {
    type O = (Option<A::O>, B::O);

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        crate::combinators::Pair(super::Opt(&self.0), &self.1).parse(ibuf)
    }
}

} // verus!
