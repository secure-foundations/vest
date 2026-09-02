//! Executable implementation for sequential formats discarding their prefix.
use crate::core::exec::output::*;
use crate::{
    combinators::Pair,
    core::{
        exec::{
            input::InputBuf,
            parser::{PResult, Parser},
            serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
            ParseError,
        },
        spec::{SafeParser, SpecByteLen, SpecParser, SpecSerializer},
    },
};
use vstd::prelude::*;
use OutputBuf;

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
    AVal: DeepView<V = AVal> + PartialEq + Structural,
 {
    type PT = B::PT;

    open spec fn exec_inv(&self) -> bool {
        &&& Pair(&self.a, &self.b).exec_inv()
        &&& forall|v: AVal| v.deep_view() == v
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (va, v)) = Pair(&self.a, &self.b).parse(ibuf)?;
        if va == self.a_val {
            Ok((n, v))
        } else {
            Err(ParseError::non_canonical())
        }
    }
}

impl<Output: OutputBuf, A, AVal, B, T, const CHECK: bool> Serializer<Output, T> for super::Preceded<
    A,
    AVal,
    B,
    CHECK,
> where
    AVal: DeepView<V = AVal>,
    T: DeepView,
    A: Serializer<Output, AVal>,
    B: Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.a.exec_inv()
        &&& self.b.exec_inv()
        &&& forall|v: AVal| v.deep_view() == v
    }

    fn serialize_into(&self, v: &T, obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        self.a.serialize_into(&self.a_val, obuf);
        self.b.serialize_into(v, obuf);

    }
}

impl<A, AVal, B, BVal, const CHECK: bool> ByteLen<BVal> for super::Preceded<
    A,
    AVal,
    B,
    CHECK,
> where AVal: DeepView<V = AVal>, BVal: DeepView, A: ByteLen<AVal>, B: ByteLen<BVal> {
    open spec fn exec_inv(&self) -> bool {
        &&& self.a.exec_inv()
        &&& self.b.exec_inv()
        &&& forall|v: AVal| v.deep_view() == v
    }

    fn length(&self, v: &BVal) -> (len: usize) {
        self.a.length(&self.a_val) + self.b.length(v)
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> Prepare<BVal> for super::Preceded<
    A,
    AVal,
    B,
    CHECK,
> where AVal: DeepView<V = AVal>, BVal: DeepView, A: Prepare<AVal>, B: Prepare<BVal> {
    open spec fn exec_inv(&self) -> bool {
        &&& self.a.exec_inv()
        &&& self.b.exec_inv()
        &&& forall|v: AVal| v.deep_view() == v
    }

    fn prepare(&self, v: &BVal) -> (checked: Result<usize, PreSerializeError>) {
        let la = self.a.prepare(&self.a_val)?;
        let lb = self.b.prepare(v)?;
        if let Some(total) = la.checked_add(lb) {
            Ok(total)
        } else {
            Err(PreSerializeError::length_too_large())
        }
    }
}

} // verus!
