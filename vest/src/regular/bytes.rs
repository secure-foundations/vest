use crate::properties::*;
use vstd::prelude::*;

use super::modifier::AndThen;

verus! {

/// Combinator for parsing and serializing a fixed number of bytes (dynamically known).
pub struct Variable(pub usize);

impl View for Variable {
    type V = Variable;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Variable {
    /// Spec version of [`Self::and_then`]
    pub open spec fn spec_and_then<Next: SpecCombinator>(self, next: Next) -> AndThen<Variable, Next> {
        AndThen(self, next)
    }

    /// Chains this combinator with another combinator.
    pub fn and_then<'a, I, O, Next: Combinator<I, O>>(self, next: Next) -> (o: AndThen<
        Variable,
        Next,
    >) where
        I: VestPublicInput,
        O: VestPublicOutput<I>,
        Next::V: SecureSpecCombinator<Type = <Next::Type as View>::V>,

        ensures
            o@ == self@.spec_and_then(next@),
    {
        AndThen(self, next)
    }
}

impl SpecCombinator for Variable {
    type Type = Seq<u8>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        if self.0 <= s.len() {
            Ok((self.0, s.subrange(0, self.0 as int)))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        if v.len() == self.0 {
            Ok(v)
        } else {
            Err(())
        }
    }
}

impl SecureSpecCombinator for Variable {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    open spec fn is_productive(&self) -> bool {
        self.0 > 0
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        assert(s1.add(s2).len() == s1.len() + s2.len());
        if let Ok((n, v)) = self.spec_parse(s1) {
            assert(s1.add(s2).subrange(0, n as int) == s1.subrange(0, n as int))
        } else {
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if let Ok(buf) = self.spec_serialize(v) {
            assert(v.subrange(0, v.len() as int) == v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<I, O> Combinator<I, O> for Variable where I: VestInput, O: VestOutput<I> {
    type Type = I;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(self.0)
    }

    fn length(&self) -> Option<usize> {
        Some(self.0)
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        if self.0 <= s.len() {
            let s_ = s.subrange(0, self.0);
            Ok((self.0, s_))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> (res: Result<
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

/// Combinator for parsing and serializing a fixed number of bytes (statically known).
pub struct Fixed<const N: usize>;

impl<const N: usize> View for Fixed<N> {
    type V = Fixed<N>;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl<const N: usize> SpecCombinator for Fixed<N> {
    type Type = Seq<u8>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        if N <= s.len() {
            Ok((N, s.subrange(0, N as int)))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        if v.len() == N {
            Ok(v)
        } else {
            Err(())
        }
    }
}

impl<const N: usize> SecureSpecCombinator for Fixed<N> {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    open spec fn is_productive(&self) -> bool {
        N > 0
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        assert(s1.add(s2).len() == s1.len() + s2.len());
        if let Ok((n, v)) = self.spec_parse(s1) {
            assert(s1.add(s2).subrange(0, n as int) == s1.subrange(0, n as int))
        } else {
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if let Ok(buf) = self.spec_serialize(v) {
            assert(v.subrange(0, v.len() as int) == v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<const N: usize, I, O> Combinator<I, O> for Fixed<N> where I: VestInput, O: VestOutput<I> {
    type Type = I;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(N)
    }

    fn length(&self) -> Option<usize> {
        Some(N)
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        if N <= s.len() {
            let s_ = s.subrange(0, N);
            Ok((N, s_))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if v.len() <= data.len() && v.len() == N && pos <= data.len() - v.len() {
            data.set_range(pos, &v);
            assert(data@.subrange(pos as int, pos + N as int) == self@.spec_serialize(v@).unwrap());
            Ok(N)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

/// Combinator that returns the rest of the input bytes from the current position.
pub struct Tail;

impl View for Tail {
    type V = Tail;

    open spec fn view(&self) -> Self::V {
        Tail
    }
}

impl SpecCombinator for Tail {
    type Type = Seq<u8>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        if s.len() <= usize::MAX {
            Ok((s.len() as usize, s))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        if v.len() <= usize::MAX {
            Ok(v)
        } else {
            Err(())
        }
    }
}

impl SecureSpecCombinator for Tail {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        assert(buf.subrange(0, buf.len() as int) == buf);
    }

    open spec fn is_prefix_secure() -> bool {
        false
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    open spec fn is_productive(&self) -> bool {
        false
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<I: VestInput, O: VestOutput<I>> Combinator<I, O> for Tail {
    type Type = I;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        Ok(((s.len()), s))
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if pos <= data.len() {
            if v.len() <= data.len() - pos {
                data.set_range(pos, &v);
                assert(data@.subrange(pos as int, pos + v@.len() as int) == self@.spec_serialize(
                    v@,
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
