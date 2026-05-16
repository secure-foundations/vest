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

impl<A, B, BVal, AVal, const CHECK: bool> Serializer<AVal> for super::Terminated<
    A,
    B,
    BVal,
    CHECK,
> where
    AVal: DeepView<V = A::SVal>,
    BVal: SelfView + Copy,
    A: Serializer<AVal>,
    B: Serializer<BVal, SVal = BVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn ex_serialize(&self, v: AVal, obuf: &mut Vec<u8>) {
        proof {
            self.b_val.self_view();
        }
        Pair(&self.a, &self.b).ex_serialize((v, self.b_val), obuf);
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> Compliance<AVal> for super::Terminated<
    A,
    B,
    BVal,
    CHECK,
> where AVal: DeepView, BVal: SelfView + Copy, A: Compliance<AVal>, B: Compliance<BVal> {
    fn check_compliance(&self, v: AVal) -> (yes: bool) {
        proof {
            self.b_val.self_view();
        }
        Pair(&self.a, &self.b).check_compliance((v, self.b_val))
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> ByteLen<AVal> for super::Terminated<
    A,
    B,
    BVal,
    CHECK,
> where AVal: DeepView, BVal: SelfView + Copy, A: ByteLen<AVal>, B: ByteLen<BVal> {
    fn length(&self, v: AVal) -> (len: usize) {
        proof {
            self.b_val.self_view();
        }
        Pair(&self.a, &self.b).length((v, self.b_val))
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> Prepare<AVal> for super::Terminated<
    A,
    B,
    BVal,
    CHECK,
> where AVal: DeepView, BVal: SelfView + Copy, A: Prepare<AVal>, B: Prepare<BVal> {
    fn prepare(&self, v: AVal) -> (checked: Result<usize, PreSerializeError>) {
        proof {
            self.b_val.self_view();
        }
        Pair(&self.a, &self.b).prepare((v, self.b_val))
    }
}

} // verus!
