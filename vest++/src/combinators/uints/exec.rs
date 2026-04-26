use crate::core::exec::input::InputBuf;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::Serializer,
    ParseError,
};
use vstd::prelude::*;

verus! {

impl Parser<&[u8]> for super::U8 {
    type PT = u8;

    open spec fn exec_inv(&self) -> bool {
        true
    }

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        if ibuf.len() < 1 {
            Err(ParseError::unexpected_eof())
        } else {
            Ok((1, ibuf[0]))
        }
    }
}

impl Serializer<u8> for super::U8 {
    fn ex_serialize(&self, v: &u8, obuf: &mut Vec<u8>) {
        obuf.push(*v);
    }
}

} // verus!
