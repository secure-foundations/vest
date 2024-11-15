use super::*;
use vstd::slice::*;

verus! {

/// Combinator for parsing and serializing a fixed number of bytes (dynamically known).
pub struct SecBytes(pub usize);

impl View for SecBytes {
    type V = SecBytes;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

// impl SecBytes {
//     /// Spec version of [`Self::and_then`]
//     pub open spec fn spec_and_then<Next: SpecCombinator>(self, next: Next) -> AndThen<SecBytes, Next> {
//         AndThen(self, next)
//     }

//     /// Chains this combinator with another combinator.
//     pub fn and_then<Next: Combinator>(self, next: Next) -> (o: AndThen<SecBytes, Next>) where
//         Next::V: SecureSpecCombinator<SpecResult = <Next::Owned as View>::V>,

//         ensures
//             o@ == self@.spec_and_then(next@),
//     {
//         AndThen(self, next)
//     }
// }

impl SpecCombinator for SecBytes {
    type SpecResult = Seq<u8>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if self.0 <= s.len() {
            Ok((self.0, s.subrange(0, self.0 as int)))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if v.len() == self.0 {
            Ok(v)
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
    }
}

impl SecureSpecCombinator for SecBytes {
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

impl SecCombinator for SecBytes {
    type Result<'a> = &'a [SecByte];

    type Owned = Vec<SecByte>;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(self.0)
    }

    fn length(&self) -> Option<usize> {
        Some(self.0)
    }

    fn parse<'a>(&self, s: &'a [SecByte]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        if self.0 <= s.len() {
            let s_ = slice_subrange(s, 0, self.0);
            assert(s_.deep_view() == s.deep_view().subrange(0, self.0 as int));
            Ok((self.0, s_))
        } else {
            Err(ParseError::UnexpectedEndOfInput)
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<SecByte>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        if v.len() <= data.len() && v.len() == self.0 && pos <= data.len() - v.len() {
            set_range_secret(data, pos, v);
            assert(data.deep_view().subrange(pos as int, pos + self.0 as int) == self@.spec_serialize(
                v.deep_view(),
            ).unwrap());
            Ok(self.0)
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
