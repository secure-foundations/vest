use crate::properties::*;
use vstd::prelude::*;

use super::repeat::RepeatResult;

verus! {

/// A combinator to parse/serialize the inner combinator C
/// zero or more times until the end of the buffer.
///
/// If the inner combinator fails before the end of the buffer,
/// `Star` will return the parsed items so far.
pub struct Star<C>(pub C);

impl<C: View> View for Star<C> {
    type V = Star<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        Star(self.0@)
    }
}

impl<C: SecureSpecCombinator> Star<C> {
    /// Helper function for spec_parse()
    pub closed spec fn spec_parse_helper(
        &self,
        s: Seq<u8>,
        res: Seq<C::Type>,
        consumed: usize,
        len: usize,
    ) -> Result<(usize, Seq<C::Type>), ()>
        decreases s.len(),
    {
        match self.0.spec_parse(s) {
            Ok((n, v)) => if 0 < n <= s.len() && consumed + n <= len {
                self.spec_parse_helper(s.skip(n as int), res.push(v), (consumed + n) as usize, len)
            } else {
                Err(())
            },
            Err(..) => Ok((consumed, res)),
        }
    }

    pub closed spec fn spec_serialize_helper(&self, v: Seq<C::Type>, res: Seq<u8>) -> Result<
        Seq<u8>,
        (),
    >
        decreases v.len(),
    {
        if v.len() == 0 {
            Ok(res)
        } else {
            match self.0.spec_serialize(v[0]) {
                Ok(s) => if s.len() != 0 {
                    self.spec_serialize_helper(v.drop_first(), res + s)
                } else {
                    Err(())
                },
                Err(..) => Err(()),
            }
        }
    }
}

impl<C: SecureSpecCombinator> Star<C> {
    proof fn theorem_parse_serialize_roundtrip_helper(
        &self,
        s: Seq<u8>,
        vs: Seq<C::Type>,
        consumed: usize,
        len: usize,
    )
        requires
            C::is_prefix_secure(),
            s.len() <= usize::MAX,
            consumed <= len,
            self.spec_serialize(vs) == Ok::<_, ()>(s.take(consumed as int)),
        ensures
            self.spec_parse_helper(s, vs, consumed, len) matches Ok((consumed, v))
                ==> self.spec_serialize(v) == Ok::<_, ()>(s.take(consumed as int)),
        decreases s.len(),
    {
        self.lemma_parse_length_helper(s, vs, consumed, len);
        match self.0.spec_parse(s) {
            Ok((n, v)) => if 0 < n <= s.len() && consumed + n <= len {
                self.0.theorem_parse_serialize_roundtrip(s);
                assert(self.0.spec_serialize(v) == Ok::<_, ()>(s.take(n as int)));
                admit();
                assume(self.spec_serialize(vs.push(v)) == Ok::<_, ()>(
                    s.skip(n as int).take(consumed + n as int),
                ));
                self.theorem_parse_serialize_roundtrip_helper(
                    s.skip(n as int),
                    vs.push(v),
                    (consumed + n) as usize,
                    len,
                );

            } else {
            },
            Err(..) => {},
        }

    }

    proof fn lemma_parse_length_helper(
        &self,
        s: Seq<u8>,
        res: Seq<C::Type>,
        consumed: usize,
        len: usize,
    )
        requires
            consumed <= len,
        ensures
            self.spec_parse_helper(s, res, consumed, len) matches Ok((m, _)) ==> m <= len,
        decreases s.len(),
    {
        match self.0.spec_parse(s) {
            Ok((n, v)) => if 0 < n <= s.len() && consumed + n <= len {
                self.lemma_parse_length_helper(
                    s.skip(n as int),
                    res.push(v),
                    (consumed + n) as usize,
                    len,
                )
            } else {
            },
            Err(..) => {},
        }
    }
}

impl<C: SecureSpecCombinator> SpecCombinator for Star<C> {
    type Type = Seq<C::Type>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()>
        decreases s.len(),
    {
        if !C::is_prefix_secure() {
            Err(())
        } else {
            self.spec_parse_helper(s, seq![], 0, s.len() as usize)
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()>
        decreases v.len(),
    {
        if !C::is_prefix_secure() {
            Err(())
        } else {
            self.spec_serialize_helper(v, seq![])
        }
    }
}

impl<C: SecureSpecCombinator> SecureSpecCombinator for Star<C> {
    /// Prepending bytes to the buffer may result in more items parsed
    /// so Star is not prefix secure
    open spec fn is_prefix_secure() -> bool {
        false
    }

    open spec fn is_productive(&self) -> bool {
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
        decreases v.len(),
    {
        admit();
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        decreases buf.len(),
    {
        if C::is_prefix_secure() {
            assert(Seq::<u8>::empty() == buf.take(0));
            self.theorem_parse_serialize_roundtrip_helper(buf, seq![], 0, buf.len() as usize);
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.lemma_parse_length_helper(s, seq![], 0, s.len() as usize);
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<I, O, C> Combinator<I, O> for Star<C> where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<I, O>,
    C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
 {
    type Type = RepeatResult<C::Type>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires() && C::V::is_prefix_secure()
    }

    #[verifier::external_body]
    fn parse(&self, mut input: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let mut res = Vec::new();
        let mut consumed: usize = 0;
        loop {
            match self.0.parse(input.clone()) {
                Ok((n, v)) => {
                    // check for infinite loop
                    if n > 0 {
                        if let Some(next_consumed) = consumed.checked_add(n) {
                            consumed = next_consumed;
                        } else {
                            return Err(ParseError::SizeOverflow);
                        }
                        res.push(v);
                        input = input.subrange(n, input.len());
                    } else {
                        return Err(ParseError::RepeatEmptyElement);
                    }
                },
                Err(..) => return Ok((consumed, RepeatResult(res))),
            }
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires() && C::V::is_prefix_secure()
    }

    #[verifier::external_body]
    fn serialize(&self, mut vs: Self::Type, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let mut len: usize = 0;
        loop {
            if vs.0.len() == 0 {
                return Ok(len);
            }
            if pos > usize::MAX - len || pos + len > data.len() {
                return Err(SerializeError::InsufficientBuffer);
            }
            match self.0.serialize(vs.0.remove(0), data, pos + len) {
                Ok(n) => {
                    if let Some(next_len) = len.checked_add(n) {
                        len = next_len;
                    } else {
                        return Err(SerializeError::SizeOverflow);
                    }
                    if n == 0 {
                        return Err(SerializeError::RepeatEmptyElement);
                    }
                },
                Err(e) => return Err(e),
            }
        }
    }
}

} // verus!
