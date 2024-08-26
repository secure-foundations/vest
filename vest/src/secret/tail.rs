use super::*;
use crate::properties::*;
use crate::regular::tail::{spec_parse_tail, spec_serialize_tail};
use vstd::prelude::*;

verus! {

pub exec fn sec_parse_tail(s: SecStream) -> (res: SecParseResult<SecBytes>)
    ensures
        prop_sec_parse_exec_spec_equiv_on(s, res, |s| spec_parse_tail(s)),
{
    if s.start < 0 {
        Err(ParseError::NegativeIndex)
    } else if s.start > s.data.length() {
        Err(ParseError::Eof)
    } else {
        let n = s.data.length();
        // data is the rest of the input starting from s.start
        let data = s.data.subrange(s.start, n);
        Ok((SecStream { start: n, ..s }, (n - s.start), data))
    }
}

pub exec fn sec_serialize_tail(s: SecStream, v: SecBytes) -> (res: SecSerializeResult)
    ensures
        prop_sec_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_tail(s, v)),
{
    if s.start < 0 {
        Err(SerializeError::NegativeIndex)
    } else if s.start > usize::MAX - v.length() {
        Err(SerializeError::IntegerOverflow)
    } else if s.start + v.length() > s.data.length() {
        Err(SerializeError::NotEnoughSpace)
    } else if v.length() != s.data.length() - s.start {
        Err(SerializeError::TailLengthMismatch)
    } else {
        let n = v.length();
        let mut data = s.data.subrange(0, s.start);
        let mut v = v;
        data.append(&mut v);
        Ok((SecStream { start: s.start + n, data }, n))
    }
}

} // verus!
