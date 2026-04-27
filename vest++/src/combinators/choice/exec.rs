use crate::core::{
    exec::{
        parser::{PResult, Parser},
        serializer::Serializer,
        ParseErrorKind,
    },
    spec::SpecParser,
};
use vstd::prelude::*;

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

impl<A, B, STA, STB> Serializer<super::Sum<STA, STB>> for super::Choice<A, B> where
    STA: DeepView<V = A::SVal>,
    STB: DeepView<V = B::SVal>,
    A: Serializer<STA>,
    B: Serializer<STB>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn ex_serialize(&self, v: super::Sum<STA, STB>, obuf: &mut Vec<u8>) {
        match v {
            super::Sum::Inl(va) => self.0.ex_serialize(va, obuf),
            super::Sum::Inr(vb) => self.1.ex_serialize(vb, obuf),
        }
    }
}

impl<I, A, B> Parser<I> for super::Alt<A, B> where
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

impl<A, B, STA, STB> Serializer<super::Sum<STA, STB>> for super::Sum<A, B> where
    STA: DeepView<V = A::SVal>,
    STB: DeepView<V = B::SVal>,
    A: Serializer<STA>,
    B: Serializer<STB>,
 {
    open spec fn exec_inv(&self) -> bool {
        match self {
            super::Sum::Inl(a) => a.exec_inv(),
            super::Sum::Inr(b) => b.exec_inv(),
        }
    }

    fn ex_serialize(&self, v: super::Sum<STA, STB>, obuf: &mut Vec<u8>) {
        match (self, v) {
            (super::Sum::Inl(a), super::Sum::Inl(va)) => a.ex_serialize(va, obuf),
            (super::Sum::Inr(b), super::Sum::Inr(vb)) => b.ex_serialize(vb, obuf),
            _ => (),
        }
    }
}

} // verus!
