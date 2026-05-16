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
impl<I, A, AVal, B> Parser<I> for super::Preceded<A, AVal, B, false> where
    I: InputBuf,
    A: Parser<I, PT = AVal> + SafeParser<PVal = AVal>,
    B: Parser<I> + SafeParser,
    AVal: DeepView<V = AVal>,
 {
    type PT = B::PT;

    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (_, v)) = Pair(&self.a, &self.b).parse(ibuf)?;
        Ok((n, v))
    }
}

// Non-malleable version
impl<I, A, AVal, B> Parser<I> for super::Preceded<A, AVal, B, true> where
    I: InputBuf,
    A: Parser<I, PT = AVal> + SafeParser<PVal = AVal>,
    B: Parser<I> + SafeParser,
    AVal: SelfView,
 {
    type PT = B::PT;

    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (va, v)) = Pair(&self.a, &self.b).parse(ibuf)?;
        if SelfView::eq(&va, &self.a_val) {
            Ok((n, v))
        } else {
            Err(ParseError::non_canonical())
        }
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> Serializer<BVal> for super::Preceded<
    A,
    AVal,
    B,
    CHECK,
> where
    AVal: SelfView + Copy,
    BVal: DeepView<V = B::SVal>,
    A: Serializer<AVal, SVal = AVal>,
    B: Serializer<BVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn ex_serialize(&self, v: BVal, obuf: &mut Vec<u8>) {
        proof {
            self.a_val.self_view();
        }
        Pair(&self.a, &self.b).ex_serialize((self.a_val, v), obuf);
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> Compliance<BVal> for super::Preceded<
    A,
    AVal,
    B,
    CHECK,
> where AVal: SelfView + Copy, BVal: DeepView, A: Compliance<AVal>, B: Compliance<BVal> {
    fn check_compliance(&self, v: BVal) -> (yes: bool) {
        proof {
            self.a_val.self_view();
        }
        Pair(&self.a, &self.b).check_compliance((self.a_val, v))
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> ByteLen<BVal> for super::Preceded<
    A,
    AVal,
    B,
    CHECK,
> where AVal: SelfView + Copy, BVal: DeepView, A: ByteLen<AVal>, B: ByteLen<BVal> {
    fn length_checked(&self, v: BVal) -> (len: Option<usize>) {
        proof {
            self.a_val.self_view();
        }
        crate::combinators::Pair(&self.a, &self.b).length_checked((self.a_val, v))
    }

    fn length(&self, v: BVal) -> (len: usize) {
        proof {
            self.a_val.self_view();
        }
        Pair(&self.a, &self.b).length((self.a_val, v))
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> Prepare<BVal> for super::Preceded<
    A,
    AVal,
    B,
    CHECK,
> where AVal: SelfView + Copy, BVal: DeepView, A: Prepare<AVal>, B: Prepare<BVal> {
    fn prepare(&self, v: BVal) -> (checked: Result<usize, PreSerializeError>) {
        proof {
            self.a_val.self_view();
        }
        Pair(&self.a, &self.b).prepare((self.a_val, v))
    }
}

} // verus!
