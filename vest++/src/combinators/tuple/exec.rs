use crate::core::{
    exec::{
        input::InputBuf,
        parser::{PResult, Parser},
    },
    spec::{SafeParser, SpecParser},
};
use vstd::prelude::*;

verus! {

impl<I, A, B> Parser<I> for super::Pair<A, B> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,
 {
    type O = (A::O, B::O);

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        assert(self.exec_inv());

        let (na, va) = self.0.parse(ibuf)?;
        proof {
            self.0.lemma_parse_safe(ibuf@);
        }
        let rest = ibuf.skip(na);
        let (nb, vb) = self.1.parse(&rest)?;

        let _total_len = ibuf.len();
        proof {
            self.1.lemma_parse_safe(rest@);
            assert(na + nb <= _total_len);
        }
        let nab = na + nb;
        let pair = (va, vb);
        assert(self.spec_parse(ibuf@) == Some((nab as int, pair.deep_view())));
        Ok((nab, pair))
    }
}

} // verus!
