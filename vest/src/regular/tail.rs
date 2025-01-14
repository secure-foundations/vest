use crate::properties::*;
use vstd::prelude::*;

verus! {

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

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
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
