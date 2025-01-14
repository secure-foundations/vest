use crate::properties::*;
use vstd::prelude::*;

use super::bytes::Bytes;

verus! {

/// Combinator that monadically chains two combinators.
pub struct AndThen<Prev, Next>(pub Prev, pub Next);

impl<Prev: View, Next: View> View for AndThen<Prev, Next> {
    type V = AndThen<Prev::V, Next::V>;

    open spec fn view(&self) -> Self::V {
        AndThen(self.0@, self.1@)
    }
}

impl<Next: SpecCombinator> SpecCombinator for AndThen<Bytes, Next> {
    type Type = Next::Type;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        if let Ok((n, v1)) = self.0.spec_parse(s) {
            if let Ok((m, v2)) = self.1.spec_parse(v1) {
                // !! for security, can only proceed if the `Next` parser consumed the entire
                // !! output from the `Prev` parser
                if m == n {
                    Ok((n, v2))
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        if let Ok(buf1) = self.1.spec_serialize(v) {
            self.0.spec_serialize(buf1)
        } else {
            Err(())
        }
    }
}

impl<Next: SecureSpecCombinator> SecureSpecCombinator for AndThen<Bytes, Next> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if let Ok(buf1) = self.1.spec_serialize(v) {
            self.1.theorem_serialize_parse_roundtrip(v);
            self.0.theorem_serialize_parse_roundtrip(buf1);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, v1)) = self.0.spec_parse(buf) {
            if let Ok((m, v2)) = self.1.spec_parse(v1) {
                self.0.theorem_parse_serialize_roundtrip(buf);
                self.1.theorem_parse_serialize_roundtrip(v1);
                if m == n {
                    if let Ok(buf2) = self.1.spec_serialize(v2) {
                        if let Ok(buf1) = self.0.spec_serialize(buf2) {
                            assert(buf1 == buf.subrange(0, n as int));
                        }
                    }
                }
            }
        }
    }

    open spec fn is_prefix_secure() -> bool {
        Bytes::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, buf: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(buf, s2);
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if let Ok((n, v1)) = self.0.spec_parse(s) {
            self.0.lemma_parse_length(s);
            self.1.lemma_parse_length(v1);
        }
    }

    open spec fn parse_productive() -> bool {
        Bytes::parse_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<I, O, Next: Combinator<I, O>> Combinator<I, O> for AndThen<Bytes, Next> where
    I: VestInput,
    O: VestOutput<I>,
    Next::V: SecureSpecCombinator<Type = <Next::Type as View>::V>,
 {
    type Type = Next::Type;

    open spec fn spec_length(&self) -> Option<usize> {
        // self.0.spec_length()
        <_ as Combinator<I, O>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        // self.0.length()
        <_ as Combinator<I, O>>::length(&self.0)
    }

    open spec fn parse_requires(&self) -> bool {
        self.1.parse_requires()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, v1) = <_ as Combinator<I, O>>::parse(&self.0, s)?;
        let (m, v2) = self.1.parse(v1)?;
        if m == n {
            Ok((n, v2))
        } else {
            Err(ParseError::AndThenUnusedBytes)
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.1.serialize_requires()
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> Result<usize, SerializeError> {
        let n = self.1.serialize(v, data, pos)?;
        if n == self.0.0 {
            Ok(n)
        } else {
            Err(SerializeError::AndThenUnusedBytes)
        }
    }
}

} // verus!
