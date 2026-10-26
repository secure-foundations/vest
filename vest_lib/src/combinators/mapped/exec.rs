//! Executable mapper interfaces and mapped-format implementations.
use super::spec::{BiMap, SpecMap};
use crate::core::exec::fns::Map;
use crate::core::exec::output::*;
use crate::core::{
    exec::{
        parser::{PResult, Parser},
        serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    },
    spec::{SpecParser, SpecSerializer},
};
use vstd::prelude::*;

verus! {

impl<I, Inner, M, MRev> Parser<I> for super::Mapped<Inner, BiMap<M, MRev>> where
    I: View<V = Seq<u8>>,
    Inner: Parser<I>,
    M: Map<Inner::PT, Input = Inner::PVal>,
    MRev: SpecMap<Input = M::Output, Output = M::Input>,
 {
    type PT = M::O;

    fn min_byte_len(&self) -> usize {
        self.inner.min_byte_len()
    }

    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, value) = self.inner.parse(ibuf)?;
        Ok((n, self.mapper.0.map(value)))
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
