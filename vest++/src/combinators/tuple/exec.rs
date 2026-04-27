use crate::core::{
    exec::{
        input::InputBuf,
        parser::{PResult, Parser},
        serializer::Serializer,
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
    type PT = (A::PT, B::PT);

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
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

impl<A, B, STA, STB> Serializer<(STA, STB)> for super::Pair<A, B> where
    STA: DeepView<V = A::SVal>,
    STB: DeepView<V = B::SVal>,
    A: Serializer<STA>,
    B: Serializer<STB>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn ex_serialize(&self, v: (STA, STB), obuf: &mut Vec<u8>) {
        self.0.ex_serialize(v.0, obuf);
        self.1.ex_serialize(v.1, obuf);
    }
}

} // verus!
