use crate::core::{
    exec::{
        parser::{PResult, Parser},
        serializer::{ByteLen, Compliance, PreSerializeError, Prepare, Serializer},
    },
    spec::SpecSerializer,
};
use vstd::prelude::*;

verus! {

impl<I, Inner> Parser<I> for super::Named<Inner> where I: View<V = Seq<u8>>, Inner: Parser<I> {
    type PT = Inner::PT;

    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        match self.0.parse(ibuf) {
            Ok((n, v)) => Ok((n, v)),
            Err(err) => Err(err.push_format(self.1)),
        }
    }
}

impl<ST, Inner> Serializer<ST> for super::Named<Inner> where
    ST: DeepView<V = Inner::SVal>,
    Inner: Serializer<ST> + SpecSerializer,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        self.0.ex_serialize(v, obuf);
    }
}

impl<T, Inner> Compliance<T> for super::Named<Inner> where T: DeepView, Inner: Compliance<T> {
    fn check_compliance(&self, v: T) -> (yes: bool) {
        self.0.check_compliance(v)
    }
}

impl<T, Inner> ByteLen<T> for super::Named<Inner> where T: DeepView, Inner: ByteLen<T> {
    fn length(&self, v: T) -> (len: usize) {
        self.0.length(v)
    }
}

impl<T, Inner> Prepare<T> for super::Named<Inner> where T: DeepView, Inner: Prepare<T> {
    fn prepare(&self, v: T) -> (checked: Result<usize, PreSerializeError>) {
        match self.0.prepare(v) {
            Err(PreSerializeError::NotCompliant(_)) => Err(PreSerializeError::NotCompliant(self.1)),
            otherwise => otherwise,
        }
    }
}

} // verus!
