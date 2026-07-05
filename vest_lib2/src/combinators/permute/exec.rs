use crate::core::exec::serializer::{PreSerializeError, Prepare};
use vstd::prelude::*;

verus! {

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
        crate::combinators::Pair(&self.0, &self.1).prepare(v)
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
        crate::combinators::Pair(&self.0, super::Permute2(&self.1, &self.2)).prepare(v)
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
        crate::combinators::Pair(&self.0, super::Permute3(&self.1, &self.2, &self.3)).prepare(v)
    }
}

} // verus!
