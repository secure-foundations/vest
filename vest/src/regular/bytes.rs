use crate::properties::*;
use vstd::prelude::*;

use super::and_then::AndThen;

verus! {

/// Combinator for parsing and serializing a fixed number of bytes (dynamically known).
pub struct Bytes(pub usize);

impl View for Bytes {
    type V = Bytes;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Bytes {
    /// Spec version of [`Self::and_then`]
    pub open spec fn spec_and_then<Next: SpecCombinator>(self, next: Next) -> AndThen<Bytes, Next> {
        AndThen(self, next)
    }

    /// Chains this combinator with another combinator.
    pub fn and_then<'a, I, O, Next: Combinator<I, O>>(self, next: Next) -> (o: AndThen<
        Bytes,
        Next,
    >) where
        I: VestInput,
        O: VestOutput<I>,
        Next::V: SecureSpecCombinator<Result = <Next::Result as View>::V>,

        ensures
            o@ == self@.spec_and_then(next@),
    {
        AndThen(self, next)
    }
}

impl SpecCombinator for Bytes {
    type Result = Seq<u8>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Result), ()> {
        if self.0 <= s.len() {
            Ok((self.0, s.subrange(0, self.0 as int)))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::Result) -> Result<Seq<u8>, ()> {
        if v.len() == self.0 {
            Ok(v)
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
    }
}

impl SecureSpecCombinator for Bytes {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Result) {
        if let Ok(buf) = self.spec_serialize(v) {
            assert(v.subrange(0, v.len() as int) == v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
    }
}

impl<I, O> Combinator<I, O> for Bytes where I: VestSecretInput, O: VestSecretOutput<I> {
    type Result = I;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(self.0)
    }

    fn length(&self) -> Option<usize> {
        Some(self.0)
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Result), ParseError>) {
        if self.0 <= s.len() {
            let s_ = s.subrange(0, self.0);
            Ok((self.0, s_))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::Result, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if v.len() <= data.len() && v.len() == self.0 && pos <= data.len() - v.len() {
            data.set_range(pos, &v);
            assert(data@.subrange(pos as int, pos + self.0 as int) == self@.spec_serialize(
                v@,
            ).unwrap());
            Ok(self.0)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
