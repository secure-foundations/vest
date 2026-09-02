//! Executable mapper interfaces and mapped-format implementations.
use super::spec::{BiMap, SpecMap};
use crate::core::exec::fns::Map;
use crate::core::exec::output::*;
use crate::core::spec::SoundParser;
use crate::core::{
    exec::{
        fns::Pred,
        input::InputSlice,
        parser::{PResult, Parser},
        serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
        ParseError,
    },
    spec::{SpecParser, SpecSerializer},
};
use core::marker::PhantomData;
use vstd::prelude::*;
use OutputBuf;

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
    M: Map<Inner::PT, Input = Inner::PVal>,
    MRev: SpecMap<Input = M::Output, Output = M::Input>,
 {
    type PT = M::O;

    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
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

impl<Output: OutputBuf, Inner, M, MRev, T> Serializer<Output, T> for super::Mapped<
    Inner,
    BiMap<M, MRev>,
> where
    T: DeepView,
    M: SpecMap<Input = MRev::Output, Output = T::V>,
    MRev: SpecMap<Input = T::V> + for <'x>Map<&'x T>,
    Inner: for <'x>Serializer<Output, <MRev as Map<&'x T>>::O>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn serialize_into(&self, v: &T, obuf: &mut Output) {
        let inner_v = self.mapper.1.map(v);
        proof {
            assert(self.spec_serialize(v.deep_view()) == self.inner.spec_serialize(
                inner_v.deep_view(),
            ));
        }
        self.inner.serialize_into(&inner_v, obuf);
    }
}

impl<Inner, M, MRev, T> Prepare<T> for super::Mapped<Inner, BiMap<M, MRev>> where
    T: DeepView,
    M: SpecMap<Input = MRev::Output, Output = T::V>,
    MRev: SpecMap<Input = T::V> + for <'x>Map<&'x T>,
    Inner: for <'x>Prepare<<MRev as Map<&'x T>>::O>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn prepare(&self, v: &T) -> Result<usize, PreSerializeError> {
        let inner_v = self.mapper.1.map(v);
        self.inner.prepare(&inner_v)
    }
}

impl<Inner, M, MRev, T> ByteLen<T> for super::Mapped<Inner, BiMap<M, MRev>> where
    T: DeepView,
    M: SpecMap<Input = MRev::Output, Output = T::V>,
    MRev: SpecMap<Input = T::V> + for <'x>Map<&'x T>,
    Inner: for <'x>ByteLen<<MRev as Map<&'x T>>::O>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn length(&self, v: &T) -> usize {
        let inner_v = self.mapper.1.map(v);
        self.inner.length(&inner_v)
    }
}

} // verus!
