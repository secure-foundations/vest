use crate::combinators::Optional;
use crate::core::exec::{
    input::InputBuf,
    parser::{PResult, Parser},
    serializer::{ByteLen, Compliance, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::core::spec::{Consistency, SpecByteLen};
use vstd::prelude::*;

verus! {

impl<I: InputBuf> Parser<I> for super::Tail {
    type PT = I;

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let len = ibuf.len();
        let tail = ibuf.take(len);
        proof {
            assert(tail.deep_view() == ibuf@);
        }
        Ok((len, tail))
    }
}

impl<'s> Serializer<&'s [u8]> for super::Tail {
    fn ex_serialize(&self, v: &'s [u8], obuf: &mut Vec<u8>) {
        obuf.extend_from_slice(v);
    }
}

impl<'s> Compliance<&'s [u8]> for super::Tail {
    fn check_compliance(&self, _v: &'s [u8]) -> (yes: bool) {
        true
    }
}

impl<'s> ByteLen<&'s [u8]> for super::Tail {
    fn length(&self, v: &'s [u8]) -> (len: usize) {
        v.len()
    }
}

impl<'s> Prepare<&'s [u8]> for super::Tail {
    fn prepare(&self, v: &'s [u8]) -> (checked: Result<usize, PreSerializeError>) {
        Ok(v.len())
    }
}

impl<I: InputBuf> Parser<I> for super::Eof {
    type PT = ();

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let len = ibuf.len();
        if len == 0 {
            Ok((0, ()))
        } else {
            Err(ParseError::expecting_eof())
        }
    }
}

impl Serializer<()> for super::Eof {
    fn ex_serialize(&self, _v: (), _obuf: &mut Vec<u8>) {
    }
}

impl Compliance<()> for super::Eof {
    fn check_compliance(&self, _v: ()) -> (yes: bool) {
        true
    }
}

impl ByteLen<()> for super::Eof {
    fn length(&self, _v: ()) -> (len: usize) {
        0
    }
}

impl Prepare<()> for super::Eof {
    fn prepare(&self, _v: ()) -> (checked: Result<usize, PreSerializeError>) {
        Ok(0)
    }
}

impl<A, B, AVal, BVal> Compliance<(AVal, BVal)> for super::PairRev<A, B> where
    AVal: DeepView,
    BVal: DeepView,
    A: Compliance<AVal>,
    B: Compliance<BVal>,
 {
    fn check_compliance(&self, v: (AVal, BVal)) -> (yes: bool) {
        self.1.check_compliance(v.0) && self.0.check_compliance(v.1)
    }
}

impl<A, B, AVal, BVal> ByteLen<(AVal, BVal)> for super::PairRev<A, B> where
    AVal: DeepView,
    BVal: DeepView,
    A: ByteLen<AVal>,
    B: ByteLen<BVal>,
 {
    fn length(&self, v: (AVal, BVal)) -> (len: usize) {
        let la = self.1.length(v.0);
        let lb = self.0.length(v.1);
        proof {
            assert((la + lb) as nat == la as nat + lb as nat);
        }
        la + lb
    }
}

impl<A, B, AVal, BVal> Prepare<(AVal, BVal)> for super::PairRev<A, B> where
    AVal: DeepView,
    BVal: DeepView,
    A: Prepare<AVal>,
    B: Prepare<BVal>,
 {
    fn prepare(&self, v: (AVal, BVal)) -> Result<usize, PreSerializeError> {
        let la = self.1.prepare(v.0)?;
        let lb = self.0.prepare(v.1)?;
        if let Some(total) = la.checked_add(lb) {
            Ok(total)
        } else {
            Err(PreSerializeError::LengthTooLarge)
        }
    }
}


} // verus!
