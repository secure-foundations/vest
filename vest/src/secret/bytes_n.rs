use super::*;
use crate::properties::*;
use vstd::prelude::*;
use vstd::slice::*;


verus! {

/// Combinator for parsing and serializing a fixed number of bytes (statically known).
pub struct SecBytesN<const N: usize>;

impl<const N: usize> View for SecBytesN<N> {
    type V = SecBytesN<N>;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl<const N: usize> SpecCombinator for SecBytesN<N> {
    type SpecResult = Seq<u8>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if N <= s.len() {
            Ok((N, s.subrange(0, N as int)))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if v.len() == N {
            Ok(v)
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
    }
}

impl<const N: usize> SecureSpecCombinator for SecBytesN<N> {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        assert(s1.add(s2).len() == s1.len() + s2.len());
        if let Ok((n, v)) = self.spec_parse(s1) {
            assert(s1.add(s2).subrange(0, n as int) == s1.subrange(0, n as int))
        } else {
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok(buf) = self.spec_serialize(v) {
            assert(v.subrange(0, v.len() as int) == v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
    }
}

impl<const N: usize> SecCombinator for SecBytesN<N> {
    type Result<'a> = &'a [SecByte];

    type Owned = Vec<SecByte>;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(N)
    }

    fn length(&self) -> Option<usize> {
        Some(N)
    }

    fn parse<'a>(&self, s: &'a [SecByte]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        if N <= s.len() {
            let s_ = slice_subrange(s, 0, N);
            assert(s_.deep_view() == s.deep_view().subrange(0, N as int)); 
            Ok((N, s_))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<SecByte>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if v.len() <= data.len() && v.len() == N && pos < data.len() - v.len() {
            set_range_secret(data, pos, v);
            assert(data.deep_view().subrange(pos as int, pos + N as int) == self@.spec_serialize(v.deep_view()).unwrap());
            Ok(N)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
    

// verus! {

// pub exec fn parse_sec_bytes(s: SecStream, n: usize) -> (res: SecParseResult<SecBytes>)
//     ensures
//         prop_sec_parse_exec_spec_equiv_on(s, res, |s| spec_parse_bytes(s, n as nat)),
// {
//     if s.start < 0 {
//         Err(ParseError::NegativeIndex)
//     } else if s.start > s.data.length() {
//         Err(ParseError::Eof)
//     } else if s.start > usize::MAX - n {
//         Err(ParseError::IntegerOverflow)
//     } else if s.start + n > s.data.length() {
//         Err(ParseError::NotEnoughData)
//     } else {
//         let data = s.data.subrange(s.start, s.start + n);
//         Ok((SecStream { start: s.start + n, ..s }, n, data))
//     }
// }

// pub exec fn serialize_sec_bytes(s: SecStream, v: SecBytes, n: usize) -> (res: SecSerializeResult)
//     ensures
//         prop_sec_serialize_exec_spec_equiv_on(
//             s,
//             v,
//             res,
//             |s, v| spec_serialize_bytes(s, v, n as nat),
//         ),
// {
//     if s.start < 0 {
//         Err(SerializeError::NegativeIndex)
//     } else if s.start > usize::MAX - v.length() {
//         Err(SerializeError::IntegerOverflow)
//     } else if s.start + v.length() > s.data.length() {
//         Err(SerializeError::NotEnoughSpace)
//     } else if v.length() != n {
//         Err(SerializeError::BytesLengthMismatch)
//     } else {
//         let mut data = s.data.subrange(0, s.start);
//         let mut rem = s.data.subrange(s.start + n, s.data.length());
//         let mut v = v;
//         data.append(&mut v);
//         data.append(&mut rem);
//         Ok((SecStream { start: s.start + n, data }, n))
//     }
// }

// } // verus!
