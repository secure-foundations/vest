use super::spec::{BiMap, SpecMap};
use crate::core::exec::fns::{Map, MapRef};
use crate::core::spec::SoundParser;
use crate::core::{
    exec::{
        fns::Pred,
        input::InputSlice,
        parser::{PResult, Parser},
        serializer::Serializer,
        ParseError,
    },
    spec::{SpecParser, SpecSerializer},
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
impl<I, Inner, M, MRev> Parser<I> for super::Mapped<Inner, BiMap<M, MRev>> where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,
    M: Map<Inner::PT, SpecI = Inner::PVal>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,
 {
    type PT = M::O;

    open spec fn exec_inv(&self) -> bool {
        &&& self.inner.exec_inv()
        &&& self.mapper.0.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        match self.inner.parse(ibuf) {
            Ok((n, v)) => {
                let mapped = self.mapper.0.map(v);
                assert(self.spec_parse(ibuf@) == Some((n as int, mapped.deep_view())));
                Ok((n, mapped))
            },
            Err(err) => Err(err),
        }
    }
}

pub broadcast proof fn lemma_map_exec_inv<I, Inner, M, MRev>(
    fmt: &super::Mapped<Inner, BiMap<M, MRev>>,
) where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,
    M: Map<Inner::PT, SpecI = Inner::PVal>,
    MRev: SpecMap<SpecI = M::SpecO, SpecO = M::SpecI>,

    requires
        fmt.inner.exec_inv(),
        fmt.mapper.0.exec_inv(),
    ensures
        #[trigger] fmt.exec_inv(),
{
}

impl<Inner, M, MRev, ST> Serializer<ST> for super::Mapped<Inner, BiMap<M, MRev>> where
    ST: DeepView,
    M: SpecMap<SpecI = Inner::SVal, SpecO = ST::V>,
    MRev: MapRef<ST, SpecI = M::SpecO, SpecO = M::SpecI>,
    Inner: Serializer<<MRev as MapRef<ST>>::O>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.inner.exec_inv()
        &&& self.mapper.1.exec_inv()
    }

    fn ex_serialize(&self, v: &ST, obuf: &mut Vec<u8>) {
        let inner_v = self.mapper.1.map_ref(v);
        self.inner.ex_serialize(&inner_v, obuf);
    }
}

pub broadcast proof fn lemma_map_ref_exec_inv<Inner, M, MRev, ST>(
    fmt: &super::Mapped<Inner, BiMap<M, MRev>>,
) where
    ST: DeepView,
    M: SpecMap<SpecI = Inner::SVal, SpecO = ST::V>,
    MRev: MapRef<ST, SpecI = M::SpecO, SpecO = M::SpecI>,
    Inner: Serializer<<MRev as MapRef<ST>>::O>,

    requires
        fmt.inner.exec_inv(),
        fmt.mapper.1.exec_inv(),
    ensures
        #[trigger] fmt.exec_inv(),
{
}

} // verus!
