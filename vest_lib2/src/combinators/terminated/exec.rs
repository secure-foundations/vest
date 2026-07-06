use crate::{
    combinators::Pair,
    core::{
        exec::{
            input::InputBuf,
            parser::{PResult, Parser},
            serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
            ParseError,
        },
        spec::{SafeParser, SpecParser, SpecSerializer},
    },
};
use vstd::prelude::*;

verus! {

// Malleable version
impl<I, A, B, BVal> Parser<I> for super::Terminated<A, B, BVal, false> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I, PT = BVal> + SafeParser<PVal = BVal>,
    BVal: DeepView<V = BVal>,
 {
    type PT = A::PT;

    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (v, _)) = Pair(&self.a, &self.b).parse(ibuf)?;
        Ok((n, v))
    }
}

// Non-malleable version
impl<I, A, B, BVal> Parser<I> for super::Terminated<A, B, BVal, true> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I, PT = BVal> + SafeParser<PVal = BVal>,
    BVal: DeepView<V = BVal> + PartialEq + Structural,
 {
    type PT = A::PT;

    open spec fn exec_inv(&self) -> bool {
        &&& Pair(&self.a, &self.b).exec_inv()
        &&& forall|v: BVal| v.deep_view() == v
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (v, vb)) = Pair(&self.a, &self.b).parse(ibuf)?;
        if vb == self.b_val {
            Ok((n, v))
        } else {
            Err(ParseError::non_canonical())
        }
    }
}

impl<A, B, BVal, T, const CHECK: bool> Serializer<T> for super::Terminated<A, B, BVal, CHECK> where
    T: DeepView,
    BVal: DeepView<V = BVal>,
    A: Serializer<T>,
    B: Serializer<BVal>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.a.exec_inv()
        &&& self.b.exec_inv()
        &&& forall|v: BVal| v.deep_view() == v
    }

    fn serialize(&self, v: &T, obuf: &mut Vec<u8>) {
        self.a.serialize(v, obuf);
        self.b.serialize(&self.b_val, obuf);
    }
}

impl<A, B, BVal, T, const CHECK: bool> ByteLen<T> for super::Terminated<A, B, BVal, CHECK> where
    T: DeepView,
    BVal: DeepView<V = BVal>,
    A: ByteLen<T>,
    B: ByteLen<BVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.a.exec_inv()
        &&& self.b.exec_inv()
        &&& forall|v: BVal| v.deep_view() == v
    }

    fn length(&self, v: &T) -> (len: usize) {
        self.a.length(v) + self.b.length(&self.b_val)
    }
}

impl<A, B, BVal, T, const CHECK: bool> Prepare<T> for super::Terminated<A, B, BVal, CHECK> where
    T: DeepView,
    BVal: DeepView<V = BVal>,
    A: Prepare<T>,
    B: Prepare<BVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.a.exec_inv()
        &&& self.b.exec_inv()
        &&& forall|v: BVal| v.deep_view() == v
    }

    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        let la = self.a.prepare(v)?;
        let lb = self.b.prepare(&self.b_val)?;
        if let Some(total) = la.checked_add(lb) {
            Ok(total)
        } else {
            Err(PreSerializeError::length_too_large())
        }
    }
}

} // verus!
