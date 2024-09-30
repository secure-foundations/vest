use crate::properties::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// Combinator for parsing and serializing a fixed number of bytes (statically known).
pub struct BytesN<const N: usize>;

impl<const N: usize> View for BytesN<N> {
    type V = BytesN<N>;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl<const N: usize> SpecCombinator for BytesN<N> {
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

impl<const N: usize> SecureSpecCombinator for BytesN<N> {
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

impl<const N: usize> Combinator for BytesN<N> {
    type Result<'a> = &'a [u8];

    type Owned = Vec<u8>;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(N)
    }

    fn length(&self) -> Option<usize> {
        Some(N)
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        if N <= s.len() {
            let s_ = slice_subrange(s, 0, N);
            Ok((N, s_))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if v.len() <= data.len() && v.len() == N && pos < data.len() - v.len() {
            set_range(data, pos, v);
            assert(data@.subrange(pos as int, pos + N as int) == self@.spec_serialize(v@).unwrap());
            Ok(N)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
