use super::*;
use crate::properties::*;
use crate::regular::bytes::{spec_parse_bytes, spec_serialize_bytes};
use vstd::prelude::*;

verus! {

pub exec fn parse_sec_bytes(s: SecStream, n: usize) -> (res: SecParseResult<SecBytes>)
    ensures
        prop_sec_parse_exec_spec_equiv_on(s, res, |s| spec_parse_bytes(s, n as nat)),
{
    if s.start < 0 {
        Err(ParseError::NegativeIndex)
    } else if s.start > s.data.length() {
        Err(ParseError::Eof)
    } else if s.start > usize::MAX - n {
        Err(ParseError::IntegerOverflow)
    } else if s.start + n > s.data.length() {
        Err(ParseError::NotEnoughData)
    } else {
        let data = s.data.subrange(s.start, s.start + n);
        Ok((SecStream { start: s.start + n, ..s }, n, data))
    }
}

pub exec fn serialize_sec_bytes(s: SecStream, v: SecBytes, n: usize) -> (res: SecSerializeResult)
    ensures
        prop_sec_serialize_exec_spec_equiv_on(
            s,
            v,
            res,
            |s, v| spec_serialize_bytes(s, v, n as nat),
        ),
{
    if s.start < 0 {
        Err(SerializeError::NegativeIndex)
    } else if s.start > usize::MAX - v.length() {
        Err(SerializeError::IntegerOverflow)
    } else if s.start + v.length() > s.data.length() {
        Err(SerializeError::NotEnoughSpace)
    } else if v.length() != n {
        Err(SerializeError::BytesLengthMismatch)
    } else {
        let mut data = s.data.subrange(0, s.start);
        let mut rem = s.data.subrange(s.start + n, s.data.length());
        let mut v = v;
        data.append(&mut v);
        data.append(&mut rem);
        Ok((SecStream { start: s.start + n, data }, n))
    }
}

} // verus!
