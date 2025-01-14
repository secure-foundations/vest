use crate::properties::*;
use vstd::prelude::*;

use super::depend::SpecDepend;

verus! {

impl<Fst: SecureSpecCombinator, Snd: SpecCombinator> SpecCombinator for (Fst, Snd) {
    type Type = (Fst::Type, Snd::Type);

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        SpecDepend { fst: self.0, snd: |r: Fst::Type| self.1 }.spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        SpecDepend { fst: self.0, snd: |r: Fst::Type| self.1 }.spec_serialize(v)
    }
}

impl<Fst: SecureSpecCombinator, Snd: SecureSpecCombinator> SecureSpecCombinator for (Fst, Snd) {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        SpecDepend { fst: self.0, snd: |r: Fst::Type| self.1 }.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        SpecDepend { fst: self.0, snd: |r: Fst::Type| self.1 }.theorem_parse_serialize_roundtrip(
            buf,
        )
    }

    open spec fn is_prefix_secure() -> bool {
        Fst::is_prefix_secure() && Snd::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, buf: Seq<u8>, s2: Seq<u8>) {
        SpecDepend { fst: self.0, snd: |r: Fst::Type| self.1 }.lemma_prefix_secure(buf, s2)
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        SpecDepend { fst: self.0, snd: |r: Fst::Type| self.1 }.lemma_parse_length(s)
    }
}

impl<Fst, Snd, I, O> Combinator<I, O> for (Fst, Snd) where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
 {
    type Type = (Fst::Type, Snd::Type);

    open spec fn spec_length(&self) -> Option<usize> {
        if let Some(n) = self.0.spec_length() {
            if let Some(m) = self.1.spec_length() {
                if n <= usize::MAX - m {
                    Some((n + m) as usize)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    fn length(&self) -> Option<usize> {
        if let Some(n) = self.0.length() {
            if let Some(m) = self.1.length() {
                if n <= usize::MAX - m {
                    Some(n + m)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires() && self.1.parse_requires() && Fst::V::is_prefix_secure()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (n, v1) = self.0.parse(s.clone())?;
        let s_ = s.subrange(n, s.len());
        let (m, v2) = self.1.parse(s_)?;
        if n <= usize::MAX - m {
            Ok(((n + m), (v1, v2)))
        } else {
            Err(ParseError::SizeOverflow)
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires() && self.1.serialize_requires() && Fst::V::is_prefix_secure()
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let n = self.0.serialize(v.0, data, pos)?;
        if n <= usize::MAX - pos && n + pos <= data.len() {
            let m = self.1.serialize(v.1, data, pos + n)?;
            if m <= usize::MAX - n {
                assert(data@.subrange(pos as int, pos + n + m as int) == self@.spec_serialize(
                    v@,
                ).unwrap());
                assert(data@ == seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));
                Ok(n + m)
            } else {
                Err(SerializeError::SizeOverflow)
            }
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
