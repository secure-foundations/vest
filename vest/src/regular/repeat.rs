use crate::properties::*;
use vstd::prelude::*;

verus! {

/// A combinator to repeatedly parse/serialize the inner combinator C
/// until the end of the buffer.
///
/// If the inner combinator fails before the end of the buffer, Repeat fails
pub struct Repeat<'x, C>(pub C, pub &'x ());

/// Wrappers around Vec so that their View's can be implemented as DeepView
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RepeatResult<T>(pub Vec<T>);

impl<C: View, 'x> Repeat<C, 'x> where C::V: SecureSpecCombinator {
    /// Constructs a new `Repeat` combinator, only if the inner combinator is productive.
    pub fn new(c: C) -> (o: Self)
        requires
            c@.is_productive(),
        ensures
            o == Self(c, &()),
    {
        Repeat(c, &())
    }
}

impl<C: View, 'x> View for Repeat<C, 'x> {
    type V = Repeat<<C as View>::V, 'x>;

    open spec fn view(&self) -> Self::V {
        Repeat(self.0@, self.1)
    }
}

impl<T: View> View for RepeatResult<T> {
    type V = Seq<T::V>;

    open spec fn view(&self) -> Self::V {
        Seq::new(self.0.len() as nat, |i: int| self.0@[i]@)
    }
}

impl<C: SecureSpecCombinator> SpecCombinator for Repeat<C, '_> {
    type Type = Seq<C::Type>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()>
        decreases s.len(),
    {
        if !C::is_prefix_secure() {
            Err(())
        } else if s.len() == 0 {
            Ok((0, seq![]))
        } else {
            match self.0.spec_parse(s) {
                Ok((n, v)) => if 0 < n <= s.len() {
                    match self.spec_parse(s.skip(n as int)) {
                        Ok((_, vs)) => Ok((s.len() as usize, seq![v] + vs)),
                        Err(..) => Err(()),
                    }
                } else {
                    Err(())
                },
                Err(..) => Err(()),
            }
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()>
        decreases v.len(),
    {
        if !C::is_prefix_secure() {
            Err(())
        } else if v.len() == 0 {
            Ok(seq![])
        } else {
            match self.0.spec_serialize(v[0]) {
                Ok(s) => if s.len() != 0 {
                    match self.spec_serialize(v.drop_first()) {
                        Ok(rest) => if s.len() + rest.len() <= usize::MAX {
                            Ok(s + rest)
                        } else {
                            Err(())
                        },
                        Err(..) => Err(()),
                    }
                } else {
                    Err(())
                },
                Err(..) => Err(()),
            }
        }
    }
}

impl<C: SecureSpecCombinator> SecureSpecCombinator for Repeat<C, '_> {
    /// Prepending bytes to the buffer may result in more items parsed
    /// so Repeat is not prefix secure
    open spec fn is_prefix_secure() -> bool {
        false
    }

    open spec fn is_productive(&self) -> bool {
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
        decreases v.len(),
    {
        if v.len() == 0 {
            assert(self.spec_serialize(v) matches Ok(b) ==> self.spec_parse(b).unwrap() =~= (0, v));
        } else {
            if self.spec_serialize(v).is_ok() {
                let s = self.0.spec_serialize(v[0]).unwrap();
                let rest = self.spec_serialize(v.drop_first()).unwrap();

                self.theorem_serialize_parse_roundtrip(v.drop_first());
                self.0.theorem_serialize_parse_roundtrip(v[0]);

                // Some technical assumptions (e.g. C should not parse a different
                // value when the buffer is extended with more bytes)
                if C::is_prefix_secure() && s.len() + rest.len() <= usize::MAX {
                    self.0.lemma_prefix_secure(s, rest);
                    let (n, _) = self.0.spec_parse(s + rest).unwrap();
                    self.0.lemma_parse_length(s + rest);

                    assert((s + rest).skip(n as int) =~= rest);
                    assert(seq![v[0]] + v.drop_first() == v);
                }
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        decreases buf.len(),
    {
        if buf.len() == 0 {
            let empty: Seq<u8> = seq![];
            assert(buf.subrange(0, 0) =~= empty);
        } else {
            if let Ok((n, v)) = self.spec_parse(buf) {
                let (n1, v1) = self.0.spec_parse(buf).unwrap();
                let (n2, v2) = self.spec_parse(buf.skip(n1 as int)).unwrap();

                self.theorem_parse_serialize_roundtrip(buf.skip(n1 as int));
                self.0.theorem_parse_serialize_roundtrip(buf);

                if C::is_prefix_secure() {
                    assert(v2 == v.drop_first());
                    assert(buf.subrange(0, n1 as int) + buf.skip(n1 as int).subrange(0, n2 as int)
                        == buf.subrange(0, n as int));
                }
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

// impl<C, 'x> Repeat<C, 'x> where  {
// /// Helper function for parse()
// /// TODO: Recursion is not ideal, but hopefully tail call opt will kick in
// fn parse_helper<I, O>(&self, s: I, res: &mut Vec<C::Type>) -> (r: Result<(), ParseError>) where
//     I: VestInput,
//     O: VestOutput<I>,
//     C: Combinator<I, O>,
//     C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
//
//     requires
//         self.0.parse_requires(),
//         C::V::is_prefix_secure(),
//         self.0@.is_productive(),
//     ensures
//         r is Ok ==> {
//             &&& self@.spec_parse(s@) is Ok
//             &&& self@.spec_parse(s@) matches Ok((n, v)) ==> RepeatResult(*res)@
//                 =~= RepeatResult(*old(res))@ + v
//         },
//         r is Err ==> self@.spec_parse(s@) is Err,
// {
//     if s.len() == 0 {
//         return Ok(());
//     }
//     let (n, v) = self.0.parse(s.clone())?;
//
//     assert(n > 0) by {
//         self.0@.lemma_parse_productive(s@);
//     }
//     res.push(v);
//     // self.parse_helper(slice_subrange(s, n, s.len()), res)
//     self.parse_helper(s.subrange(n, s.len()), res)
// }
// fn serialize_helper<I, O>(
//     &self,
//     v: &'x RepeatResult<C::Type>,
//     data: &mut O,
//     pos: usize,
//     len: usize,
// ) -> (res: Result<usize, SerializeError>) where
//     I: VestInput,
//     O: VestOutput<I>,
//     C: Combinator<I, O>,
//     C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
//
//     requires
//         self.0.serialize_requires(),
//         C::V::is_prefix_secure(),
//         self.0@.is_productive(),
//     ensures
//         data@.len() == old(data)@.len(),
//         res matches Ok(n) ==> {
//             &&& self@.spec_serialize(old(v)@) is Ok
//             &&& self@.spec_serialize(old(v)@) matches Ok(s) ==> n == (len + s.len()) && data@
//                 =~= seq_splice(old(data)@, (pos + len) as usize, s)
//         },
// {
//     if pos > usize::MAX - len || pos + len > data.len() {
//         return Err(SerializeError::InsufficientBuffer);
//     }
//     if v.0.len() == 0 {
//         assert(data@ =~= seq_splice(old(data)@, pos, seq![]));
//         return Ok(len);
//     }
//     let n1 = self.0.serialize(v.0.remove(0), data, pos + len)?;
//
//     assert(v@ =~= old(v)@.drop_first());
//
//     assert(n1 > 0) by {
//         self.0@.lemma_serialize_productive(old(v)@[0]);
//     }
//     let ghost data2 = data@;
//
//     if let Some(next_len) = len.checked_add(n1) {
//         self.serialize_helper(v, data, pos, next_len)
//     } else {
//         Err(SerializeError::SizeOverflow)
//     }
// }
// }
impl<I, O, C, 'x> Combinator<I, O> for Repeat<C, 'x> where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<I, O>,
    C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
    C::SType: 'x + Copy,
 {
    type Type = RepeatResult<C::Type>;

    type SType = &'x RepeatResult<C::SType>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn parse_requires(&self) -> bool {
        &&& <C as View>::V::is_prefix_secure()
        &&& self.0.parse_requires()
        &&& self.0@.is_productive()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let mut res = Vec::new();
        let mut offset: usize = 0;

        assert(s@.subrange(0, s@.len() as int) == s@);

        while offset < s.len()
            invariant
                0 <= offset <= s@.len(),
                self.parse_requires(),
                self@.spec_parse(s@.subrange(offset as int, s@.len() as int)) matches Ok((_, rest))
                    ==> {
                    &&& self@.spec_parse(s@) matches Ok((_, v))
                    &&& RepeatResult(res)@ + rest =~= v
                },
                offset < s@.len() ==> (self@.spec_parse(
                    s@.subrange(offset as int, s@.len() as int),
                ) is Err ==> self@.spec_parse(s@) is Err),
        {
            let (n, v) = self.0.parse(s.subrange(offset, s.len()))?;
            assert(n > 0) by {
                self.0@.lemma_parse_productive(s@.subrange(offset as int, s@.len() as int));
            }

            let ghost prev_offset = offset;

            res.push(v);
            offset += n;

            assert(s@.subrange(prev_offset as int, s@.len() as int).skip(n as int) =~= s@.subrange(
                offset as int,
                s@.len() as int,
            ))
        }

        let ghost empty: Seq<u8> = seq![];
        assert(s@.subrange(s@.len() as int, s@.len() as int) == empty);

        Ok(
            (s.len(), RepeatResult(res)),
        )
        // self.parse_helper(s.clone(), &mut res)?;
        // Ok((s.len(), RepeatResult(res)))

    }

    open spec fn serialize_requires(&self) -> bool {
        &&& <C as View>::V::is_prefix_secure()
        &&& self.0.serialize_requires()
        &&& self.0@.is_productive()
    }

    #[verifier::external_body]
    fn serialize(&self, mut vs: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let mut len = 0usize;
        let mut i = 0usize;
        let cnt = vs.0.len();

        if pos > data.len() {
            return Err(SerializeError::InsufficientBuffer);
        }
        let ghost old_data = data@;
        let ghost old_vs = vs@;
        assert(data@ == seq_splice(old_data, pos, seq![]));

        while i < cnt
            invariant
                0 <= i <= cnt,
                vs@.len() == cnt,
                data@.len() == old(data)@.len(),
                self.serialize_requires(),
                self@.spec_serialize(vs@) matches Ok(b) && b.len() == len && data@ == seq_splice(
                    old_data,
                    pos,
                    b,
                ),
        // res matches Ok(n) ==> {
        //     &&& self@.spec_serialize(v@) matches Ok(b)
        //     &&& b.len() == n
        //     &&& buf@ == seq_splice(old(buf)@, pos, b)
        // },
        // self@.serialize_correct(
        //     vs@.take(i as int),
        //     i,
        //     data@,
        //     old_data,
        //     pos,
        //     Ok::<_, SerializeError>(len),
        // ),
        {
            if pos > usize::MAX - len || pos + len > data.len() {
                return Err(SerializeError::InsufficientBuffer);
            }
            match self.0.serialize(vs.0[i], data, pos + len) {
                // match self.0.serialize(vs.0.remove(0), data, pos + len) {
                Ok(n) => {
                    assert(n > 0) by {
                        self.0@.lemma_serialize_productive(vs@[i as int]);
                    }
                    if let Some(next_len) = len.checked_add(n) {
                        len = next_len;
                        i += 1;
                        assert(vs@.take(i as int).drop_last() == vs@.take((i - 1) as int));  // <-- key
                        let ghost spec_bytes = self@.spec_serialize(vs@.take(i as int));
                        assert(data@ == seq_splice(old_data, pos, spec_bytes.unwrap()));
                    } else {
                        return Err(SerializeError::SizeOverflow);
                    }
                },
                Err(e) => return Err(e),
            }
        }

        assert(vs@.take(i as int) =~= vs@);
        Ok(len)
    }
}

} // verus!
