use crate::combinators::mapped::spec::SpecMap;
use crate::core::exec::fns::MapRef;
use crate::core::{
    exec::{
        input::InputBuf,
        parser::{PResult, Parser},
        serializer::Serializer,
    },
    spec::{SafeParser, SpecParser, SpecSerializer},
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
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let (na, va) = self.0.parse(ibuf)?;
        let rest = ibuf.skip(na);
        let (nb, vb) = self.1.parse(&rest)?;

        let _total_len = ibuf.len();
        proof {
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

impl<I, A, B> Parser<I> for super::Bind<A, B> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B::O: Parser<I> + SafeParser,
    B: MapRef<A::PT, Input = A::PVal>,
 {
    type PT = (A::PT, <B::O as Parser<I>>::PT);

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& forall|pb: B::O| #[trigger] pb.exec_inv() && pb.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let (na, key) = self.0.parse(ibuf)?;
        let rest = ibuf.skip(na);
        let next = self.1.map(&key);
        assert(next.exec_inv() && next.safe_inv());
        let (nb, val) = next.parse(&rest)?;

        let _total_len = ibuf.len();
        proof {
            assert(na + nb <= _total_len);
        }
        let nab = na + nb;
        let pair = (key, val);
        Ok((nab, pair))
    }
}

impl<A, B, STA, STB> Serializer<(STA, STB)> for super::Bind<A, B> where
    STA: DeepView<V = A::SVal>,
    STB: DeepView<V = <B::O as SpecSerializer>::SVal>,
    A: Serializer<STA>,
    B::O: Serializer<STB>,
    B: MapRef<STA, Input = A::SVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& forall|pb: B::O| pb.exec_inv()
    }

    fn ex_serialize(&self, v: (STA, STB), obuf: &mut Vec<u8>) {
        let next = self.1.map(&v.0);
        self.0.ex_serialize(v.0, obuf);
        next.ex_serialize(v.1, obuf);
    }
}


} // verus!
