use crate::core::{
    exec::{
        parser::{PResult, Parser},
        serializer::{ByteLen, Compliance, ComplianceErrorKind, PreSerializeError, Prepare, Serializer},
        ParseError,
    },
    spec::SpecParser,
};
use vstd::prelude::*;

verus! {

impl<I, Inner> Parser<I> for super::Cond<Inner> where I: View<V = Seq<u8>>, Inner: Parser<I> {
    type PT = Inner::PT;

    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        if self.0 {
            self.1.parse(ibuf)
        } else {
            Err(ParseError::cond_rejected())
        }
    }
}

impl<Inner, ST> Serializer<ST> for super::Cond<Inner> where
    ST: DeepView<V = Inner::SVal>,
    Inner: Serializer<ST>,
 {
    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        self.1.ex_serialize(v, obuf);
    }
}

impl<T, Inner> Compliance<T> for super::Cond<Inner> where T: DeepView, Inner: Compliance<T> {
    fn check_compliance(&self, v: T) -> (yes: bool) {
        self.0 && self.1.check_compliance(v)
    }
}

impl<T, Inner> ByteLen<T> for super::Cond<Inner> where T: DeepView, Inner: ByteLen<T> {
    fn length(&self, v: T) -> (len: usize) {
        self.1.length(v)
    }
}

impl<T, Inner> Prepare<T> for super::Cond<Inner> where T: DeepView, Inner: Prepare<T> {
    fn prepare(&self, v: T) -> (checked: Result<usize, PreSerializeError>) {
        if self.0 {
            self.1.prepare(v)
        } else {
            Err(PreSerializeError::NotCompliant(ComplianceErrorKind::CondRejected))
        }
    }
}

} // verus!
