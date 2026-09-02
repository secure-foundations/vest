//! Executable implementations for ordered alternatives.
use crate::core::exec::output::*;
use crate::core::{
    exec::{
        parser::{PResult, Parser},
        serializer::{ByteLen, ComplianceErrorKind, PreSerializeError, Prepare, Serializer},
        ParseErrorKind,
    },
    spec::{Consistency, SpecByteLen, SpecParser, SpecSerializer},
};
use vstd::prelude::*;
use OutputBuf;

verus! {

impl<A: View, B: View> View for super::Sum<A, B> {
    type V = super::Sum<A::V, B::V>;

    open spec fn view(&self) -> Self::V {
        match self {
            super::Sum::Inl(a) => super::Sum::Inl(a@),
            super::Sum::Inr(b) => super::Sum::Inr(b@),
        }
    }
}

impl<A: DeepView, B: DeepView> DeepView for super::Sum<A, B> {
    type V = super::Sum<A::V, B::V>;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            super::Sum::Inl(a) => super::Sum::Inl(a.deep_view()),
            super::Sum::Inr(b) => super::Sum::Inr(b.deep_view()),
        }
    }
}

impl<I, A, B> Parser<I> for super::Choice<A, B> where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    B: Parser<I>,
 {
    type PT = super::Sum<A::PT, B::PT>;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        match self.0.parse(ibuf) {
            Ok((n, v)) => Ok((n, super::Sum::Inl(v))),
            Err(first_err) => {
                match self.1.parse(ibuf) {
                    Ok((n, v)) => {
                        let inr_v = super::Sum::Inr(v);
                        assert(self.spec_parse(ibuf@) == Some((n as int, inr_v.deep_view())));
                        Ok((n, inr_v))
                    },
                    Err(second_err) => {
                        match first_err.kind {
                            ParseErrorKind::RecursionLimitExceeded => Err(first_err),
                            _ => Err(second_err),
                        }
                    },
                }
            },
        }
    }
}

impl<Output: OutputBuf, A, B, TA, TB> Serializer<Output, super::Sum<TA, TB>> for super::Choice<
    A,
    B,
> where TA: DeepView, TB: DeepView, A: Serializer<Output, TA>, B: Serializer<Output, TB> {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn serialize_into(&self, v: &super::Sum<TA, TB>, obuf: &mut Output) {
        match v {
            super::Sum::Inl(va) => self.0.serialize_into(va, obuf),
            super::Sum::Inr(vb) => self.1.serialize_into(vb, obuf),
        }
    }
}

impl<A, B, TA, TB> ByteLen<super::Sum<TA, TB>> for super::Choice<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: ByteLen<TA>,
    B: ByteLen<TB>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn length(&self, v: &super::Sum<TA, TB>) -> (len: usize) {
        match v {
            super::Sum::Inl(va) => self.0.length(va),
            super::Sum::Inr(vb) => self.1.length(vb),
        }
    }
}

impl<A, B, TA, TB> Prepare<super::Sum<TA, TB>> for super::Choice<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn prepare(&self, v: &super::Sum<TA, TB>) -> (checked: Result<usize, PreSerializeError>) {
        match v {
            super::Sum::Inl(va) => self.0.prepare(va),
            super::Sum::Inr(vb) => self.1.prepare(vb),
        }
    }
}

impl<const NONDETERMINISTIC: bool, I, A, B> Parser<I> for super::Alt<A, B, NONDETERMINISTIC> where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    B: Parser<I, PVal = A::PVal, PT = A::PT>,
 {
    type PT = A::PT;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        match self.0.parse(ibuf) {
            Ok(r) => Ok(r),
            Err(_) => self.1.parse(ibuf),
        }
    }
}

impl<I, A, B> Parser<I> for super::Sum<A, B> where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    B: Parser<I>,
 {
    type PT = super::Sum<A::PT, B::PT>;

    open spec fn exec_inv(&self) -> bool {
        match self {
            super::Sum::Inl(a) => a.exec_inv(),
            super::Sum::Inr(b) => b.exec_inv(),
        }
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        match self {
            super::Sum::Inl(a) => {
                let (n, v) = a.parse(ibuf)?;
                Ok((n, super::Sum::Inl(v)))
            },
            super::Sum::Inr(b) => {
                let (n, v) = b.parse(ibuf)?;
                Ok((n, super::Sum::Inr(v)))
            },
        }
    }
}

impl<Output: OutputBuf, A, B, TA, TB> Serializer<Output, super::Sum<TA, TB>> for super::Sum<
    A,
    B,
> where TA: DeepView, TB: DeepView, A: Serializer<Output, TA>, B: Serializer<Output, TB> {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        match self {
            super::Sum::Inl(a) => a.exec_inv(),
            super::Sum::Inr(b) => b.exec_inv(),
        }
    }

    fn serialize_into(&self, v: &super::Sum<TA, TB>, obuf: &mut Output) {
        match (self, v) {
            (super::Sum::Inl(a), super::Sum::Inl(va)) => a.serialize_into(va, obuf),
            (super::Sum::Inr(b), super::Sum::Inr(vb)) => b.serialize_into(vb, obuf),
            _ => (),
        }
    }
}

impl<A, B, TA, TB> ByteLen<super::Sum<TA, TB>> for super::Sum<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: ByteLen<TA>,
    B: ByteLen<TB>,
 {
    open spec fn exec_inv(&self) -> bool {
        match self {
            super::Sum::Inl(a) => a.exec_inv(),
            super::Sum::Inr(b) => b.exec_inv(),
        }
    }

    fn length(&self, v: &super::Sum<TA, TB>) -> (len: usize) {
        match (self, v) {
            (super::Sum::Inl(a), super::Sum::Inl(va)) => a.length(va),
            (super::Sum::Inr(b), super::Sum::Inr(vb)) => b.length(vb),
            _ => 0,
        }
    }
}

impl<A, B, TA, TB> Prepare<super::Sum<TA, TB>> for super::Sum<A, B> where
    TA: DeepView,
    TB: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,
 {
    open spec fn exec_inv(&self) -> bool {
        match self {
            super::Sum::Inl(a) => a.exec_inv(),
            super::Sum::Inr(b) => b.exec_inv(),
        }
    }

    fn prepare(&self, v: &super::Sum<TA, TB>) -> (checked: Result<usize, PreSerializeError>) {
        match (self, v) {
            (super::Sum::Inl(a), super::Sum::Inl(va)) => a.prepare(va),
            (super::Sum::Inr(b), super::Sum::Inr(vb)) => b.prepare(vb),
            _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidChoice)),
        }
    }
}

} // verus!
