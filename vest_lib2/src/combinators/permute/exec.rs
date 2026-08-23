use crate::combinators::tuple::Pair;
use crate::core::exec::output::OutputBuf;
use crate::core::exec::parser::{PResult, Parser};
use crate::core::exec::serializer::{ByteLen, PreSerializeError, Prepare, Serializer};
use vstd::prelude::*;

verus! {

impl<I, P1, P2> Parser<I> for super::Permute2<P1, P2> where
    I: crate::core::exec::input::InputBuf,
    P1: Parser<I> + crate::core::spec::SafeParser,
    P2: Parser<I> + crate::core::spec::SafeParser,
 {
    type PT = (P1::PT, P2::PT);

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        // Mirrors the left-biased `Alt` in the spec: try the declared order, then the swap.
        match Pair(&self.0, &self.1).parse(ibuf) {
            Ok((n, v)) => Ok((n, v)),
            Err(_) => match Pair(&self.1, &self.0).parse(ibuf) {
                Ok((n, (v2, v1))) => Ok((n, (v1, v2))),
                Err(e) => Err(e),
            },
        }
    }
}

impl<Output: OutputBuf, P1, P2, T1, T2> Serializer<Output, (T1, T2)> for super::Permute2<
    P1,
    P2,
> where T1: DeepView, T2: DeepView, P1: Serializer<Output, T1>, P2: Serializer<Output, T2> {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn serialize_into(&self, v: &(T1, T2), obuf: &mut Output) {
        // Serialization always emits the declared order.
        Pair(&self.0, &self.1).serialize_into(v, obuf)
    }
}

impl<P1, P2, T1, T2> ByteLen<(T1, T2)> for super::Permute2<P1, P2> where
    T1: DeepView,
    T2: DeepView,
    P1: ByteLen<T1>,
    P2: ByteLen<T2>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn length(&self, v: &(T1, T2)) -> (len: usize) {
        Pair(&self.0, &self.1).length(v)
    }
}

impl<P1, P2, T1, T2> Prepare<(T1, T2)> for super::Permute2<P1, P2> where
    T1: DeepView,
    T2: DeepView,
    P1: Prepare<T1>,
    P2: Prepare<T2>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
    }

    fn prepare(&self, v: &(T1, T2)) -> (checked: Result<usize, PreSerializeError>) {
        Pair(&self.0, &self.1).prepare(v)
    }
}

impl<I, A, B, C> Parser<I> for super::Permute3<A, B, C> where
    I: crate::core::exec::input::InputBuf,
    A: Parser<I> + crate::core::spec::SafeParser,
    B: Parser<I> + crate::core::spec::SafeParser,
    C: Parser<I> + crate::core::spec::SafeParser,
 {
    type PT = (A::PT, (B::PT, C::PT));

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
        &&& self.2.exec_inv()
        &&& self.2.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        match Pair(&self.0, super::Permute2(&self.1, &self.2)).parse(ibuf) {
            Ok((n, v)) => Ok((n, v)),
            Err(_) => match Pair(&self.1, super::Permute2(&self.0, &self.2)).parse(ibuf) {
                Ok((n, (vb, (va, vc)))) => Ok((n, (va, (vb, vc)))),
                Err(_) => match Pair(&self.2, super::Permute2(&self.0, &self.1)).parse(ibuf) {
                    Ok((n, (vc, (va, vb)))) => Ok((n, (va, (vb, vc)))),
                    Err(e) => Err(e),
                },
            },
        }
    }
}

impl<Output: OutputBuf, A, B, C, TA, TB, TC> Serializer<Output, (TA, (TB, TC))> for super::Permute3<
    A,
    B,
    C,
> where
    TA: DeepView,
    TB: DeepView,
    TC: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,
    C: Serializer<Output, TC>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
        &&& self.2.exec_inv()
    }

    fn serialize_into(&self, v: &(TA, (TB, TC)), obuf: &mut Output) {
        Pair(&self.0, super::Permute2(&self.1, &self.2)).serialize_into(v, obuf)
    }
}

impl<A, B, C, TA, TB, TC> ByteLen<(TA, (TB, TC))> for super::Permute3<A, B, C> where
    TA: DeepView,
    TB: DeepView,
    TC: DeepView,
    A: ByteLen<TA>,
    B: ByteLen<TB>,
    C: ByteLen<TC>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
        &&& self.2.exec_inv()
    }

    fn length(&self, v: &(TA, (TB, TC))) -> (len: usize) {
        Pair(&self.0, super::Permute2(&self.1, &self.2)).length(v)
    }
}

impl<I, A, B, C, D> Parser<I> for super::Permute4<A, B, C, D> where
    I: crate::core::exec::input::InputBuf,
    A: Parser<I> + crate::core::spec::SafeParser,
    B: Parser<I> + crate::core::spec::SafeParser,
    C: Parser<I> + crate::core::spec::SafeParser,
    D: Parser<I> + crate::core::spec::SafeParser,
 {
    type PT = (A::PT, (B::PT, (C::PT, D::PT)));

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
        &&& self.2.exec_inv()
        &&& self.2.safe_inv()
        &&& self.3.exec_inv()
        &&& self.3.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        match Pair(&self.0, super::Permute3(&self.1, &self.2, &self.3)).parse(ibuf) {
            Ok((n, v)) => Ok((n, v)),
            Err(_) => match Pair(&self.1, super::Permute3(&self.0, &self.2, &self.3)).parse(ibuf) {
                Ok((n, (vb, (va, (vc, vd))))) => Ok((n, (va, (vb, (vc, vd))))),
                Err(_) => match Pair(&self.2, super::Permute3(&self.0, &self.1, &self.3)).parse(
                    ibuf,
                ) {
                    Ok((n, (vc, (va, (vb, vd))))) => Ok((n, (va, (vb, (vc, vd))))),
                    Err(_) => match Pair(&self.3, super::Permute3(&self.0, &self.1, &self.2)).parse(
                        ibuf,
                    ) {
                        Ok((n, (vd, (va, (vb, vc))))) => Ok((n, (va, (vb, (vc, vd))))),
                        Err(e) => Err(e),
                    },
                },
            },
        }
    }
}

impl<Output: OutputBuf, A, B, C, D, TA, TB, TC, TD> Serializer<
    Output,
    (TA, (TB, (TC, TD))),
> for super::Permute4<A, B, C, D> where
    TA: DeepView,
    TB: DeepView,
    TC: DeepView,
    TD: DeepView,
    A: Serializer<Output, TA>,
    B: Serializer<Output, TB>,
    C: Serializer<Output, TC>,
    D: Serializer<Output, TD>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
        &&& self.2.exec_inv()
        &&& self.3.exec_inv()
    }

    fn serialize_into(&self, v: &(TA, (TB, (TC, TD))), obuf: &mut Output) {
        Pair(&self.0, super::Permute3(&self.1, &self.2, &self.3)).serialize_into(v, obuf)
    }
}

impl<A, B, C, D, TA, TB, TC, TD> ByteLen<(TA, (TB, (TC, TD)))> for super::Permute4<
    A,
    B,
    C,
    D,
> where
    TA: DeepView,
    TB: DeepView,
    TC: DeepView,
    TD: DeepView,
    A: ByteLen<TA>,
    B: ByteLen<TB>,
    C: ByteLen<TC>,
    D: ByteLen<TD>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
        &&& self.2.exec_inv()
        &&& self.3.exec_inv()
    }

    fn length(&self, v: &(TA, (TB, (TC, TD)))) -> (len: usize) {
        Pair(&self.0, super::Permute3(&self.1, &self.2, &self.3)).length(v)
    }
}

impl<A, B, C, TA, TB, TC> Prepare<(TA, (TB, TC))> for super::Permute3<A, B, C> where
    TA: DeepView,
    TB: DeepView,
    TC: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,
    C: Prepare<TC>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
        &&& self.2.exec_inv()
    }

    fn prepare(&self, v: &(TA, (TB, TC))) -> (checked: Result<usize, PreSerializeError>) {
        Pair(&self.0, super::Permute2(&self.1, &self.2)).prepare(v)
    }
}

impl<A, B, C, D, TA, TB, TC, TD> Prepare<(TA, (TB, (TC, TD)))> for super::Permute4<
    A,
    B,
    C,
    D,
> where
    TA: DeepView,
    TB: DeepView,
    TC: DeepView,
    TD: DeepView,
    A: Prepare<TA>,
    B: Prepare<TB>,
    C: Prepare<TC>,
    D: Prepare<TD>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
        &&& self.2.exec_inv()
        &&& self.3.exec_inv()
    }

    fn prepare(&self, v: &(TA, (TB, (TC, TD)))) -> (checked: Result<usize, PreSerializeError>) {
        Pair(&self.0, super::Permute3(&self.1, &self.2, &self.3)).prepare(v)
    }
}

} // verus!
