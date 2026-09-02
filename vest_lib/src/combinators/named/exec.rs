//! Executable error-context propagation for named formats.
use crate::core::exec::output::*;
use crate::core::{
    exec::{
        parser::{PResult, Parser},
        serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    },
    spec::SpecSerializer,
};
use vstd::prelude::*;
use OutputBuf;

verus! {

impl<I, Inner> Parser<I> for super::Named<Inner> where I: View<V = Seq<u8>>, Inner: Parser<I> {
    type PT = Inner::PT;

    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        match self.1.parse(ibuf) {
            Ok((n, v)) => Ok((n, v)),
            Err(err) => Err(err.push_format(self.0)),
        }
    }
}

impl<Output: OutputBuf, T, Inner> Serializer<Output, T> for super::Named<Inner> where
    T: DeepView,
    Inner: Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn serialize_into(&self, v: &T, obuf: &mut Output) {
        self.1.serialize_into(v, obuf);
    }
}

impl<T, Inner> ByteLen<T> for super::Named<Inner> where T: DeepView, Inner: ByteLen<T> {
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn length(&self, v: &T) -> (len: usize) {
        self.1.length(v)
    }
}

impl<T, Inner> Prepare<T> for super::Named<Inner> where T: DeepView, Inner: Prepare<T> {
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        match self.1.prepare(v) {
            Err(err) => Err(err.push_format(self.0)),
            otherwise => otherwise,
        }
    }
}

} // verus!
