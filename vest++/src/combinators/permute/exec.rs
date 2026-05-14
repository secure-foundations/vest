use crate::core::exec::serializer::{PreSerializeError, Prepare};
use vstd::prelude::*;

verus! {

impl<P1, P2, ST1, ST2> Prepare<(ST1, ST2)> for super::Permute2<P1, P2> where
    ST1: DeepView,
    ST2: DeepView,
    P1: Prepare<ST1>,
    P2: Prepare<ST2>,
 {
    fn prepare(&self, v: (ST1, ST2)) -> (checked: Result<usize, PreSerializeError>) {
        crate::combinators::Pair(&self.0, &self.1).prepare(v)
    }
}

impl<A, B, C, STA, STB, STC> Prepare<(STA, (STB, STC))> for super::Permute3<A, B, C> where
    STA: DeepView,
    STB: DeepView,
    STC: DeepView,
    A: Prepare<STA>,
    B: Prepare<STB>,
    C: Prepare<STC>,
 {
    fn prepare(&self, v: (STA, (STB, STC))) -> (checked: Result<usize, PreSerializeError>) {
        crate::combinators::Pair(&self.0, super::Permute2(&self.1, &self.2)).prepare(v)
    }
}

impl<A, B, C, D, STA, STB, STC, STD> Prepare<(STA, (STB, (STC, STD)))> for super::Permute4<
    A,
    B,
    C,
    D,
> where
    STA: DeepView,
    STB: DeepView,
    STC: DeepView,
    STD: DeepView,
    A: Prepare<STA>,
    B: Prepare<STB>,
    C: Prepare<STC>,
    D: Prepare<STD>,
 {
    fn prepare(&self, v: (STA, (STB, (STC, STD)))) -> (checked: Result<usize, PreSerializeError>) {
        crate::combinators::Pair(&self.0, super::Permute3(&self.1, &self.2, &self.3)).prepare(v)
    }
}

} // verus!
