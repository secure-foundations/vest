use crate::core::{
    exec::{
        parser::{PResult, Parser},
        serializer::{ByteLen, Compliance, ComplianceErrorKind, PreSerializeError, Prepare, Serializer},
    },
    spec::SpecSerializer,
};
use vstd::prelude::*;

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

impl<ST, Inner> Serializer<ST> for super::Named<Inner> where
    ST: DeepView<V = Inner::SVal>,
    Inner: Serializer<ST> + SpecSerializer,
 {
    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        self.1.ex_serialize(v, obuf);
    }
}

impl<T, Inner> Compliance<T> for super::Named<Inner> where T: DeepView, Inner: Compliance<T> {
    fn check_compliance(&self, v: T) -> (yes: bool) {
        self.1.check_compliance(v)
    }
}

impl<T, Inner> ByteLen<T> for super::Named<Inner> where T: DeepView, Inner: ByteLen<T> {
    fn length(&self, v: T) -> (len: usize) {
        self.1.length(v)
    }
}

impl<T, Inner> Prepare<T> for super::Named<Inner> where T: DeepView, Inner: Prepare<T> {
    fn prepare(&self, v: T) -> (checked: Result<usize, PreSerializeError>) {
        match self.1.prepare(v) {
            Err(PreSerializeError::NotCompliant(_)) => Err(PreSerializeError::NotCompliant(ComplianceErrorKind::NamedFormat(self.0))),
            otherwise => otherwise,
        }
    }
}

} // verus!
