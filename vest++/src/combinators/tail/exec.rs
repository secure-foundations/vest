use crate::core::exec::{
    input::InputBuf,
    parser::{PResult, Parser},
    serializer::Serializer,
    ParseError,
};
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

} // verus!
