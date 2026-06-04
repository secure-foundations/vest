use crate::combinators::mapped::spec::SpecMap;
use crate::core::exec::fns::MapRef;
use crate::core::{
    exec::{
        input::InputBuf,
        parser::{PResult, Parser},
        serializer::{ByteLen, Compliance, PreSerializeError, Prepare, Serializer},
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

impl<A, B, TA, TB> Serializer<(TA, TB)> for super::Pair<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: Serializer<TA>,
    B: Serializer<TB>,
 {
    fn serialize(&self, v: &(TA, TB), obuf: &mut Vec<u8>) {
        self.0.serialize(&v.0, obuf);
        self.1.serialize(&v.1, obuf);
    }
}

impl<A, B, TA, TB> Compliance<(TA, TB)> for super::Pair<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: Compliance<TA>,
    B: Compliance<TB>,
 {
    fn check_compliance(&self, v: &(TA, TB)) -> (yes: bool) {
        self.0.check_compliance(&v.0) && self.1.check_compliance(&v.1)
    }
}

impl<A, B, TA, TB> Prepare<(TA, TB)> for super::Pair<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,
 {
    fn prepare(&self, v: &(TA, TB)) -> Result<usize, PreSerializeError> {
        let la = self.0.prepare(&v.0)?;
        let lb = self.1.prepare(&v.1)?;
        if let Some(total) = la.checked_add(lb) {
            Ok(total)
        } else {
            Err(PreSerializeError::LengthTooLarge)
        }
    }
}

impl<A, B, TA, TB> ByteLen<(TA, TB)> for super::Pair<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: ByteLen<TA>,
    B: ByteLen<TB>,
 {
    fn length(&self, v: &(TA, TB)) -> (len: usize) {
        let la = self.0.length(&v.0);
        let lb = self.1.length(&v.1);
        la + lb
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

impl<A, B, TA, TB> Serializer<(TA, TB)> for super::Bind<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: Serializer<TA>,
    B::O: Serializer<TB>,
    B: MapRef<TA, Input = TA::V>,
 {
    fn serialize(&self, v: &(TA, TB), obuf: &mut Vec<u8>) {
        let next = self.1.map(&v.0);
        self.0.serialize(&v.0, obuf);
        next.serialize(&v.1, obuf);
    }
}

impl<A, B, STA, STB> Compliance<(STA, STB)> for super::Bind<A, B> where
    STA: DeepView,
    STB: DeepView,
    A: Compliance<STA>,
    B::O: Compliance<STB>,
    B: MapRef<STA, Input = STA::V>,
 {
    fn check_compliance(&self, v: &(STA, STB)) -> (yes: bool) {
        let next = self.1.map(&v.0);
        self.0.check_compliance(&v.0) && next.check_compliance(&v.1)
    }
}

impl<A, B, STA, STB> ByteLen<(STA, STB)> for super::Bind<A, B> where
    STA: DeepView,
    STB: DeepView,
    A: ByteLen<STA>,
    B::O: ByteLen<STB>,
    B: MapRef<STA, Input = STA::V>,
 {
    fn length(&self, v: &(STA, STB)) -> (len: usize) {
        let next = self.1.map(&v.0);
        let la = self.0.length(&v.0);
        let lb = next.length(&v.1);
        la + lb
    }
}

impl<A, B, STA, STB> Prepare<(STA, STB)> for super::Bind<A, B> where
    STA: DeepView,
    STB: DeepView,
    A: Prepare<STA>,
    B::O: Prepare<STB>,
    B: MapRef<STA, Input = STA::V>,
 {
    fn prepare(&self, v: &(STA, STB)) -> Result<usize, PreSerializeError> {
        let next = self.1.map(&v.0);
        let la = self.0.prepare(&v.0)?;
        let lb = next.prepare(&v.1)?;
        if let Some(total) = la.checked_add(lb) {
            Ok(total)
        } else {
            Err(PreSerializeError::LengthTooLarge)
        }
    }
}

} // verus!
