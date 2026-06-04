use crate::{
    combinators::Pair,
    core::{
        exec::{
            input::InputBuf,
            parser::{PResult, Parser},
            serializer::{ByteLen, Compliance, PreSerializeError, Prepare, Serializer},
            ParseError, SelfView,
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
    BVal: SelfView,
 {
    type PT = A::PT;

    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (v, vb)) = Pair(&self.a, &self.b).parse(ibuf)?;
        if SelfView::eq(&vb, &self.b_val) {
            Ok((n, v))
        } else {
            Err(ParseError::non_canonical())
        }
    }
}

impl<A, B, BVal, T, const CHECK: bool> Serializer<T> for super::Terminated<A, B, BVal, CHECK> where
    T: DeepView,
    BVal: SelfView,
    A: Serializer<T>,
    B: Serializer<BVal>,
 {
    fn serialize(&self, v: &T, obuf: &mut Vec<u8>) {
        proof {
            self.b_val.self_view();
        }
        // Pair(&self.a, &self.b).ex_serialize(&(*v, self.b_val), obuf);
        self.a.serialize(v, obuf);
        self.b.serialize(&self.b_val, obuf);
    }
}

impl<A, B, BVal, T, const CHECK: bool> Compliance<T> for super::Terminated<A, B, BVal, CHECK> where
    T: DeepView,
    BVal: SelfView,
    A: Compliance<T>,
    B: Compliance<BVal>,
 {
    fn check_compliance(&self, v: &T) -> (yes: bool) {
        proof {
            self.b_val.self_view();
        }
        self.a.check_compliance(v) && self.b.check_compliance(&self.b_val)
    }
}

impl<A, B, BVal, T, const CHECK: bool> ByteLen<T> for super::Terminated<A, B, BVal, CHECK> where
    T: DeepView,
    BVal: SelfView,
    A: ByteLen<T>,
    B: ByteLen<BVal>,
 {
    fn length(&self, v: &T) -> (len: usize) {
        proof {
            self.b_val.self_view();
        }
        self.a.length(v) + self.b.length(&self.b_val)
    }
}

impl<A, B, BVal, T, const CHECK: bool> Prepare<T> for super::Terminated<A, B, BVal, CHECK> where
    T: DeepView,
    BVal: SelfView,
    A: Prepare<T>,
    B: Prepare<BVal>,
 {
    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        proof {
            self.b_val.self_view();
        }
        let la = self.a.prepare(v)?;
        let lb = self.b.prepare(&self.b_val)?;
        if let Some(total) = la.checked_add(lb) {
            Ok(total)
        } else {
            Err(PreSerializeError::LengthTooLarge)
        }
    }
}

} // verus!
