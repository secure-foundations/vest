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

impl<A, AVal, B, T, const CHECK: bool> Serializer<T> for super::Preceded<A, AVal, B, CHECK> where
    AVal: SelfView,
    T: DeepView,
    A: Serializer<AVal>,
    B: Serializer<T>,
 {
    fn serialize(&self, v: &T, obuf: &mut Vec<u8>) {
        proof {
            self.a_val.self_view();
        }
        // Pair(&self.a, &self.b).ex_serialize(&(self.a_val, *v), obuf);
        self.a.serialize(&self.a_val, obuf);
        self.b.serialize(v, obuf);

    }
}

impl<A, AVal, B, BVal, const CHECK: bool> Compliance<BVal> for super::Preceded<
    A,
    AVal,
    B,
    CHECK,
> where AVal: SelfView, BVal: DeepView, A: Compliance<AVal>, B: Compliance<BVal> {
    fn check_compliance(&self, v: &BVal) -> (yes: bool) {
        proof {
            self.a_val.self_view();
        }
        self.a.check_compliance(&self.a_val) && self.b.check_compliance(v)
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> ByteLen<BVal> for super::Preceded<
    A,
    AVal,
    B,
    CHECK,
> where AVal: SelfView, BVal: DeepView, A: ByteLen<AVal>, B: ByteLen<BVal> {
    fn length(&self, v: &BVal) -> (len: usize) {
        proof {
            self.a_val.self_view();
        }
        self.a.length(&self.a_val) + self.b.length(v)
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> Prepare<BVal> for super::Preceded<
    A,
    AVal,
    B,
    CHECK,
> where AVal: SelfView, BVal: DeepView, A: Prepare<AVal>, B: Prepare<BVal> {
    fn prepare(&self, v: &BVal) -> (checked: Result<usize, PreSerializeError>) {
        proof {
            self.a_val.self_view();
        }
        let la = self.a.prepare(&self.a_val)?;
        let lb = self.b.prepare(v)?;
        if let Some(total) = la.checked_add(lb) {
            Ok(total)
        } else {
            Err(PreSerializeError::LengthTooLarge)
        }
    }
}

} // verus!
