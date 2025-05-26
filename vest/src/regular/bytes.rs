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
    pub open spec fn spec_and_then<Next: SpecCombinator>(self, next: Next) -> AndThen<
        Variable,
        Next,
    > {
        AndThen(self, next)
    }

    /// Chains this combinator with another combinator.
    pub fn and_then<'x, I, O, Next: Combinator<'x, I, O>>(self, next: Next) -> (o: AndThen<
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

    open spec fn wf(&self, v: Self::Type) -> bool {
        v.len() == self.0
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if self.0 <= s.len() {
            Some((self.0 as int, s.take(self.0 as int)))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        v
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
        if let Some((n, v)) = self.spec_parse(s1) {
            assert(s1.add(s2).subrange(0, n as int) == s1.subrange(0, n as int))
        } else {
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        assert(v.take(v.len() as int) == v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<'x, I, O> Combinator<'x, I, O> for Variable where I: VestInput + 'x, O: VestOutput<I> {
    type Type = I;

    type SType = &'x I;

    fn length(&self, v: Self::SType) -> usize {
        self.0
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        if self.0 <= s.len() {
            let s_ = s.subrange(0, self.0);
            Ok((self.0, s_))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if v.len() <= data.len() && pos <= data.len() - v.len() {
            data.set_range(pos, &v);
            assert(data@.subrange(pos as int, pos + self.0 as int) == self@.spec_serialize(v@));
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

    open spec fn wf(&self, v: Self::Type) -> bool {
        v.len() == N
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if N <= s.len() {
            Some((N as int, s.take(N as int)))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        v
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
        if let Some((n, v)) = self.spec_parse(s1) {
            assert(s1.add(s2).subrange(0, n as int) == s1.subrange(0, n as int))
        } else {
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        assert(v.take(v.len() as int) == v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<'x, const N: usize, I, O> Combinator<'x, I, O> for Fixed<N> where
    I: VestInput + 'x,
    O: VestOutput<I>,
 {
    type Type = I;

    type SType = &'x I;

    fn length(&self, v: Self::SType) -> usize {
        N
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        if N <= s.len() {
            let s_ = s.subrange(0, N);
            Ok((N, s_))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if v.len() <= data.len() && pos <= data.len() - v.len() {
            data.set_range(pos, &v);
            assert(data@.subrange(pos as int, pos + N as int) == self@.spec_serialize(v@));
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

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        Some((s.len() as int, s))
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        v
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

impl<'x, I: VestInput + 'x, O: VestOutput<I>> Combinator<'x, I, O> for Tail {
    type Type = I;

    type SType = &'x I;

    fn length(&self, v: Self::SType) -> usize {
        v.len()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        Ok(((s.len()), s))
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if v.len() <= data.len() - pos {
            data.set_range(pos, &v);
            assert(data@.subrange(pos as int, pos + v@.len() as int) == self@.spec_serialize(v@));
            Ok(v.len())
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
