use super::*;
use crate::properties::*;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

/// Combinator that returns the rest of the input bytes from the current position.
pub struct SecTail;

impl View for SecTail {
    type V = SecTail;

    open spec fn view(&self) -> Self::V {
        SecTail
    }
}

impl SpecCombinator for SecTail {
    type SpecResult = Seq<u8>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if s.len() <= usize::MAX {
            Ok((s.len() as usize, s))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if v.len() <= usize::MAX {
            Ok(v)
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
    }
}

impl SecureSpecCombinator for SecTail {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        assert(buf.subrange(0, buf.len() as int) == buf);
    }

    open spec fn is_prefix_secure() -> bool {
        false
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }
}

impl SecCombinator for SecTail {
    type Result<'a> = &'a [SecByte];

    type Owned = Vec<SecByte>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn parse<'a>(&self, s: &'a [SecByte]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        Ok(((s.len()), s))
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<SecByte>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if pos <= data.len() {
            if v.len() <= data.len() - pos {
                set_range_secret(data, pos, v);
                assert(data.deep_view().subrange(pos as int, pos + v.deep_view().len() as int) == self@.spec_serialize(
                    v.deep_view(),
                ).unwrap());
                Ok(v.len())
            } else {
                Err(SerializeError::InsufficientBuffer)
            }
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
    


// verus! {

// pub exec fn sec_parse_SecTail(s: SecStream) -> (res: SecParseResult<SecBytes>)
//     ensures
//         prop_sec_parse_exec_spec_equiv_on(s, res, |s| spec_parse_SecTail(s)),
// {
//     if s.start < 0 {
//         Err(ParseError::NegativeIndex)
//     } else if s.start > s.data.length() {
//         Err(ParseError::Eof)
//     } else {
//         let n = s.data.length();
//         // data is the rest of the input starting from s.start
//         let data = s.data.subrange(s.start, n);
//         Ok((SecStream { start: n, ..s }, (n - s.start), data))
//     }
// }

// pub exec fn sec_serialize_SecTail(s: SecStream, v: SecBytes) -> (res: SecSerializeResult)
//     ensures
//         prop_sec_serialize_exec_spec_equiv_on(s, v, res, |s, v| spec_serialize_SecTail(s, v)),
// {
//     if s.start < 0 {
//         Err(SerializeError::NegativeIndex)
//     } else if s.start > usize::MAX - v.length() {
//         Err(SerializeError::IntegerOverflow)
//     } else if s.start + v.length() > s.data.length() {
//         Err(SerializeError::NotEnoughSpace)
//     } else if v.length() != s.data.length() - s.start {
//         Err(SerializeError::SecTailLengthMismatch)
//     } else {
//         let n = v.length();
//         let mut data = s.data.subrange(0, s.start);
//         let mut v = v;
//         data.append(&mut v);
//         Ok((SecStream { start: s.start + n, data }, n))
//     }
// }

// } // verus!
