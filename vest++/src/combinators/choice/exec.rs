use crate::core::{
    exec::parser::{PResult, Parser},
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
    type O = super::Sum<A::O, B::O>;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        match self.0.parse(ibuf) {
            Ok((n, v)) => Ok((n, super::Sum::Inl(v))),
            Err(_) => {
                let (n, v) = self.1.parse(ibuf)?;
                let inr_v = super::Sum::Inr(v);
                assert(self.spec_parse(ibuf@) == Some((n as int, inr_v.deep_view())));
                Ok((n, inr_v))
            },
        }
    }
}

impl<I, A, B> Parser<I> for super::Alt<A, B> where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    B: Parser<I, PVal = A::PVal, O = A::O>,
 {
    type O = A::O;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
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
    type O = super::Sum<A::O, B::O>;

    open spec fn exec_inv(&self) -> bool {
        match self {
            super::Sum::Inl(a) => a.exec_inv(),
            super::Sum::Inr(b) => b.exec_inv(),
        }
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
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

} // verus!
