use crate::core::{
    exec::{
        input::InputBuf,
        parser::{PResult, Parser},
        serializer::{ByteLen, Compliance, PreSerializeError, Prepare, Serializer},
    },
    spec::{SafeParser, SpecParser},
};
use vstd::prelude::*;

verus! {

impl<I, A> Parser<I> for super::Opt<A> where I: View<V = Seq<u8>>, A: Parser<I> {
    type PT = Option<A::PT>;

    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
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

impl<A, ST> Serializer<Option<ST>> for super::Opt<A> where
    ST: DeepView<V = A::SVal>,
    A: Serializer<ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn ex_serialize(&self, v: Option<ST>, obuf: &mut Vec<u8>) {
        match v {
            Some(vv) => self.0.ex_serialize(vv, obuf),
            None => {},
        }
    }
}

impl<A, ST> ByteLen<Option<ST>> for super::Opt<A> where ST: DeepView, A: ByteLen<ST> {
    fn length(&self, v: Option<ST>) -> (len: usize) {
        match v {
            Some(vv) => self.0.length(vv),
            None => 0,
        }
    }
}

impl<A, ST> Prepare<Option<ST>> for super::Opt<A> where ST: DeepView, A: Prepare<ST> {
    fn prepare(&self, v: Option<ST>) -> (checked: Result<usize, PreSerializeError>) {
        match v {
            Some(vv) => self.0.prepare(vv),
            None => Ok(0),
        }
    }
}

impl<I, A, B> Parser<I> for super::Optional<A, B> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,
 {
    type PT = (Option<A::PT>, B::PT);

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        crate::combinators::Pair(super::Opt(&self.0), &self.1).parse(ibuf)
    }
}

impl<A, B, STA, STB> ByteLen<(Option<STA>, STB)> for super::Optional<A, B> where
    STA: DeepView,
    STB: DeepView,
    A: ByteLen<STA>,
    B: ByteLen<STB>,
 {
    fn length(&self, v: (Option<STA>, STB)) -> (len: usize) {
        crate::combinators::Pair(super::Opt(&self.0), &self.1).length(v)
    }
}

impl<A, B, STA, STB> Prepare<(Option<STA>, STB)> for super::Optional<A, B> where
    STA: DeepView,
    STB: DeepView,
    A: Prepare<STA>,
    B: Prepare<STB>,
 {
    fn prepare(&self, v: (Option<STA>, STB)) -> Result<usize, PreSerializeError> {
        crate::combinators::Pair(super::Opt(&self.0), &self.1).prepare(v)
    }
}

} // verus!
