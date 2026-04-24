use crate::core::exec::fns::Map;
use super::spec::{BiMap, SpecMap};
use crate::core::spec::SoundParser;
use crate::core::{
    exec::{
        fns::Pred,
        input::InputSlice,
        parser::{PResult, Parser},
        ParseError,
    },
    spec::SpecParser,
};
use core::marker::PhantomData;
use vstd::prelude::*;

verus! {

// impl<I, A, M> Parser<I> for super::Mapped<A, M> where
//     I: View<V = Seq<u8>>,
//     A: Parser<I>,
//     M: Mapper<I, PIn = A::O, In = A::PVal>,
//  {
//     type O = M::POut;
//     open spec fn exec_inv(&self) -> bool {
//         self.inner.exec_inv()
//     }
//     fn parse(&self, ibuf: &I) -> PResult<Self::O> {
//         let (n, v) = self.inner.parse(ibuf)?;
//         Ok((n, M::map(v)))
//     }
// }


impl<I, Inner, M, MRev> Parser<I> for super::Map<Inner, BiMap<M, MRev>> where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,
    M: Map<I = Inner::O, SpecI = Inner::PVal>,
    MRev: Map<I = M::O, O = M::I, SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    type O = M::O;

    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::O> {
        let (n, v) = self.inner.parse(ibuf)?;
        Ok((n, self.mapper.0.map(v)))
        // Ok((n, M::map(v)))

    }
}

pub broadcast proof fn lemma_map_exec_inv<I, Inner, M, MRev>(
    fmt: &super::Map<Inner, BiMap<M, MRev>>,
) where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,
    M: Map<I = Inner::O, SpecI = Inner::PVal>,
    MRev: Map<I = M::O, O = M::I, SpecI = M::SpecO, SpecO = M::SpecI>,

    requires
        fmt.inner.exec_inv(),
    ensures
        #[trigger] fmt.exec_inv(),
{
}

} // verus!
